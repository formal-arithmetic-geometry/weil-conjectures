# Worker report

Files written:

- `lem-coef-singular-span-bar-cylinder-gluing.json`: statement node, split; no Mathlib match.
- `lem-coef-singular-bar-realization-cylinder.json`: statement node, unsplit; Mathlib searches found no match.
- `lem-coef-double-cylinder-weak-equivalence-gluing.json`: statement node, unsplit; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

Attachments: none. No sorry-free declaration with the item tag or matching statement occurs under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`.

WANTED: an archived simplicial homotopy theory reference for the explicit walking-span bar-realization/double-mapping-cylinder homeomorphism, for `lem-coef-singular-bar-realization-cylinder`.

WANTED: an archived homotopy-pushout reference proving invariance of the double mapping cylinder under a weak equivalence of commuting spans, for `lem-coef-double-cylinder-weak-equivalence-gluing`.

The imported item was unsplit and had no proof. The blueprint paragraph is agent-formulated and supplies context rather than a theorem citation. The two new nodes are strict intermediate lemmas: the first identifies the bar realization with a cylinder before applying counits; the second is the general gluing invariance statement. They do not duplicate the existing `lem-coef-double-mapping-cylinder-space-pushout` node, which states the coherent pushout interpretation, or `lem-coef-singular-counit-weak-equivalence`, which states only the realization-singular counit theorem.

No part of the statement was corrected. I tested the formulas on the empty middle object (giving the disjoint union of the two ends), on an empty end (which forces the middle to be empty in the stated span), and on the point and interval spans. The hypotheses and the endpoint maps agree with the imported statement.

Nothing remains unfinished within this split; the two auxiliary lemmas are intentionally statement-only queue nodes for later workers.

## Not duplicates

- `lem-coef-singular-bar-realization-cylinder` vs `lem-coef-double-mapping-cylinder-space-pushout`: the new node is a concrete homeomorphism from a walking-span bar realization to a quotient cylinder, while the existing node states the coherent homotopy-pushout universal property of a topological double mapping cylinder.
- `lem-coef-singular-bar-realization-cylinder` vs `lem-coef-singular-counit-weak-equivalence`: the new node computes the bar realization for a strict span; the existing node concerns only the evaluation map from a realization of a singular complex.
- `lem-coef-double-cylinder-weak-equivalence-gluing` vs `lem-coef-double-mapping-cylinder-space-pushout`: the new node proves homotopy invariance under a weak equivalence of spans; the existing node identifies one cylinder as a colimit cocone.
- `lem-coef-double-cylinder-weak-equivalence-gluing` vs `lem-coef-sset-gluing-filtered-equivalences`: the new node is a topological double-cylinder statement for arbitrary commuting maps; the existing node is a simplicial pushout theorem with a monomorphism hypothesis and a separate filtered-colimit assertion.

## Review by N0

I read the imported item, the unit record `sk-prop-sf-biduality-general`, the chapter record, and the blueprint proof paragraph `prop-coef-integral-exceptional-adjoint.proof.md`, Paragraph 2. I also searched the slopmaster2 source for the item tag and for the key terms “singular span”, “bar cylinder”, and “mapping cylinder”; there is no project declaration to attach. The item statement is unchanged, including the exact definitions of `Sing`, `B_W`, the quotient `D(f,g)`, the coordinate `w`, naturality, and empty-object allowance.

For Step 1 I opened `lem-coef-singular-bar-realization-cylinder.json` and checked that its statement supplies exactly the natural homeomorphism used: it identifies `|BK_W(U)|` with the quotient of the realized span, and gives the same `w/2`, `1-w/2`, and `1/2` coordinates. The step then applies the evaluation maps to this homeomorphism; the endpoint identifications are the displayed evaluation formula. For Step 2 I opened `lem-coef-singular-counit-weak-equivalence.json` and verified that it states continuity and naturality of the evaluation map, the component bijection, and the based homotopy-group isomorphisms for every topological space without separation, connectedness, or nonemptiness hypotheses. I checked that these hypotheses apply to `|A|`, `|B|`, and `|C|`, and that naturality gives the two commuting span equations. For Step 3 I opened `lem-coef-double-cylinder-weak-equivalence-gluing.json`; its statement gives precisely the induced weak equivalence of double cylinders, the component and homotopy-group conclusions, naturality, and empty-space cases. The naturality clauses of the three cited nodes supply the target's naturality clause.

For each new node I searched the whole DAG by its key words and searched the current blueprint with `tools/blueprint_refs.py`; no existing node or blueprint node states either intermediate lemma. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for each new node and recorded the returned abstract cylinder or span primitives as no matches. The explicit edge cases were checked before writing the statements: an empty `C` removes the cylinder summand, while an empty `A` or `B` forces `C` empty under the span maps; the point and interval cases agree with the quotient coordinates. The new nodes are therefore precise intermediate claims rather than restatements of the item. Every proof step has `elementary: false`, names all non-elementary statement dependencies, and `citations.json` quotes verbatim substrings of those dependency statements. The union of the step uses equals `proof_deps`, and the blueprint ancestry and source places are filled for the item and both new nodes.
