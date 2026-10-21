# Worker report: Q129

## Files written

- dag/nodes/sec-nagata-compactification/def-nagata-strict-transform-chart-comparison-localized.json: definition, split using existing nodes; Mathlib has its generic localization ingredients, but not the entire blow-up-specific transported definition as stated.
- citations.json: empty list, since a definition has no proof steps.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. AlgebraicGeometry.AffineBlowup.strictChartComparisonAway, lean/WeilConjectures/Blowup/Affine/StrictTransformChart.lean:565, has the exact blueprint tag and a real body, but only handles s in B and has target (B_s)_{b'}, rather than the localization of the blow-up chart ring B[IB/b]. Its docstring describes the comparison after embedding the chart ring into B_b. It therefore does not supply every clause of the item. strictChartComparisonAway_eq (line 581) compares that ambient-valued map with the map of the localized B-data, also only for s in B. Neither supplies the arbitrary chart-element localization and all presentation transports requested here. I did not claim an attachment based on the tag alone, or on a partial result.

## WANTED

None. Read the current blueprint definition, chapter and unit, and the local Stacks source.

## Corrections and scope

The original definition left the rings, the localized denominators and the word "transporting" implicit. I have made its inherited context explicit: A to B is a commutative ring map, I is an ideal, a is in I, R is the strict chart, T is B[IB/b], and f is the existing comparison. The source and target of the map localized at c in R are R_c and T_{f(c)}. A base element in either A or B is inserted by its structural map. This is an expansion of the current main-20261015 definition, not a change to its intended mathematical meaning or to a target. In particular I do not assert here that a freshly reconstructed strict chart from localized data is isomorphic to R_c: that is the distinct localization-data node and its compatibility theorem.

The transport is now the literal map beta composed with f_c composed with alpha inverse. The canonical tensor presentation and iterated localization presentation are specified by their fraction formulas, using existing nodes. The blueprint's bypass note and all imported/update metadata are preserved. The source path now identifies the current snapshot (order 160), whose displayed definition was read. No unit or chapter route changed; the definition realizes the unit sentence "These descriptions commute with localization." No Lean was written and no compiler or build tool was run.

## Mathlib and duplicate searches

I searched all project Lean sources for the exact tag and strict-transform chart localization vocabulary and read StrictTransformChart.lean:249-287 and 430-597. I searched the entire DAG for iterated localization, tensor localization, 00CP and 00C9, and used blueprint_refs.py search for localization, strict-transform-chart-comparison, iterated-localization, localization at, and tensor-product-localization, plus ancestor for this item. These searches found the existing nodes reused below; no new node is needed. Other strict-chart localization and cocycle nodes state properties of this definition, not this definition itself. same_as is therefore [].

Every Mathlib query in the item was actually run through msearch.py and is present in searches.jsonl. The first semantic query returned local-ring and scheme tools, so I tried the more direct induced-map phrasing and found IsLocalization.Away.map and Localization.awayMap. Loogle found awayMap as well. The first grep used "def awayMap" and returned no hits because these are abbreviations; the corrected pattern found awayMap at Mathlib/RingTheory/Localization/Away/Basic.lean:497 and awayLift at :485. I read lines 475-508, including awayLift_mk. I also read Mathlib/RingTheory/Localization/BaseChange.lean:423-448, which gives tensorProductEquivTMulRight at :427 and its tensor formula at :438. These generic tools implement the localizing operation. Identifying and transporting this specific strict-transform comparison in its various chart presentations is additional definition data, so I retain status split rather than recording the entire item as an exact Mathlib leaf.

## Review by Q129

I read the current definition in literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-blowups/def-nagata-strict-transform-chart-comparison-localized.md in full and compared it with blueprint_update, the chapter record, and the unit's localization sentence. For the underlying construction I read Stacks algebra.tex, Definition 00CO (definition-localization) and Proposition 00CP (proposition-universal-property-localization), including the proof assigning x/s to f(x)f(s) inverse. For the tensor presentation I read Lemmas 00DK (lemma-tensor-localization) and 00DL (lemma-tensor-product-localization), with their fraction formulas and proofs. There are no new-node sources to review.

This is a definition, so proof remains [], proof_deps remains [], proof_origin remains null, and there are no proof-step citations or long proof steps. Its data and named construction dependencies were checked as follows, by opening and reading each node's statement:

1. def-nagata-strict-transform-chart-comparison defines precisely the needed map R to B[IB/b] induced on the power-torsion quotient. I used only that map, not its later bijectivity theorem, kernel proof, or a stronger localization compatibility claim. The contextual hypotheses A to B, I ideal, a in I and b the image of a were checked against its defining dependencies, including def-nagata-strict-chart-to-extended-blowup-chart and def-nagata-strict-transform-basechange-chart-ring.
2. def-weil-ring-localization-away defines fractions, their equivalence relation, their arithmetic and the structural map. This is the meaning of each R_c and T_{f(c)}. The fact that the image of the chosen denominator is invertible is part of that definition; no nonzerodivisor hypothesis is required.
3. lem-weil-pbc-localization-away-universal-property says: "Then there is a unique ring homomorphism $\bar g:R_f\to P$ with $\bar g(a/1)=g(a)$ for all $a\in R$; it is given by $\bar g(a/f^n)=g(a)\,g(f)^{-n}$." Apply with its R our R, its f our c, P=T_{f(c)} and g the composite of the comparison with T to T_{f(c)}. The required unit is f(c)/1, invertible by construction. This supplies the named well-definedness and uniqueness of the defining fraction map, rather than hiding a theorem in the definition.
4. lem-weil-pbc-algebra-localization-away-base-change states the algebra isomorphism A_g tensor_R B to (A tensor_R B)_{g tensor 1}, with exactly the displayed fraction formula. All its rings are commutative and the tensor products have the same base. It applies to the base-localization presentations and, after exchanging the two factors as its match explains, to the other tensor factor. I do not invoke it to commute the power-torsion quotient with localization.
5. lem-weil-pbc-localization-of-localization states that a localization of a localization is a localization of the original ring and gives the multiplicative subset explicitly. Together with the already cited unique-extension property it specifies the identifications over E; for E_s followed by t/1 these invert s and t. E_{st} also inverts both, since s has inverse t/(st) and t has inverse s/(st). The inverse homomorphisms are therefore the unique extensions of the identity on E. Iterated fractions represent z times s inverse to power m times t inverse to power n. The transport beta f_c alpha inverse is just composition of specified homomorphisms, not an assertion of new strict-chart base-change compatibility.

I checked the B-algebra property needed for the base-element notation in strictChartComparison's actual Lean type and its defining comparison node: the image of s in the target really is f(c). For elements from A this follows by composing A to B with the two B-algebra structural maps. These are structural identities, not extra hypotheses such as flatness, finite generation or reducedness.

For delivery-errors B through E: there is no new node to violate B1-B3, B5-B9 or duplicate checks; the existing nodes supply all construction notions. The JSON has ordinary single TeX backslashes after decoding. The partial tagged declaration was rejected as an attachment under B10. C1 and C4 are addressed by the statement-by-statement checks above; no proof or stronger property of a cited node was used. C6 is avoided because none of the references uses this localized definition: they are its original comparison or general ring-localization tools. There is no new lemma restating a clause, no moved whole proof, and no appeal to a source as a proof (D1-D5). The unit's route is preserved and all off-unit tools used here are existing Mathlib leaves.

Small cases: c=1 gives f; c=0 gives the unique map between zero rings; if f(c)=0 while c is not nilpotent, the target localization is the zero ring and the map remains defined. If A or B is the zero ring, or a=0 or I=0, the same constructions permit zero chart rings. Zero divisors cause no difficulty because equality of fractions is annihilator-based, not cancellation. For iterated localization s=0 or t=0 every presentation is zero; s=1 or t=1 removes the redundant localization. Taking E=Z, s=2, t=3 verifies that z/2^m/3^n has the stated image in Z[1/6], and the inverse sends 1/6 to (1/2)(1/3). No regularity or nonempty-spectrum assumption was silently used.

## Unfinished work

None for this one-level definition split. The defining comparison and separate localization-compatibility theorems keep their existing DAG states; they were not claimed proved by this delivery.
