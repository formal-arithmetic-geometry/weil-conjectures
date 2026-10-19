## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-valued-straightening.json`: repaired split, no Mathlib match. The statement and stage-2 Lean record are unchanged. Only the returned long arguments in steps 1, 8 and 9 are replaced by short citations; all other arguments retain their route, with TeX escapes normalized in proof text.
- `dag/nodes/sec-six-functors/lem-coef-covariant-derived-replacement-base-change.json`: new statement-only technical lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-unmarked-cone-model-comparison.json`: new statement-only technical lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-strict-opposite-realization-zigzag.json`: new statement-only technical lemma, unsplit; no Mathlib match.
- `citations.json`: every step/node pair, with a verbatim quotation of the statement actually used. In particular the new-node quotations contain their conclusions, rather than their introductory definition references.
- `prerequisite-audit.json`: fresh read-only traversal of the overlaid statement and proof prerequisite graph and the step lengths.

This delivery has **3 new nodes and 0 Mathlib leaves**. The original reports remain in `report.inherited-Q60.md` and `report.before-final-audit.md`; existing search logs and result files are retained. All writes are confined to this sandbox. No agent, compiler, Lake or build was started.

## Attachments

None. The slopmaster2 `WeilConjectures/` search for the blueprint id, straightening and relative-nerve names gives no finished declaration stating the whole item. The existing stage-2 Lean interface is preserved and is not treated as a finished proof.

## WANTED

WANTED: archival Higher Topos Theory, Theorem 2.2.1.2, Corollary 2.1.2.7, Remark 3.2.5.10, Lemma 3.2.5.17(1), Proposition 3.2.5.18(1), Proposition 4.2.4.4 and Proposition A.3.3.8, for this item and the three new technical inputs. The online IAS PDF is https://www.math.ias.edu/~lurie/papers/HTT.pdf. I read the comparison at printed pp.197–201 and the enriched-evaluation theorem at p.258 online, and checked the other hypotheses against the existing prerequisite statements and retained source-reading record. No source was downloaded into the shared repository. The new nodes remain statement-only; the item's proof remains agent-written. No Stacks tag states these higher-categorical comparisons; no SGA source is used.

## What was wrong and what changed

The human's return requires extraction of the hidden lemmas in steps 1 (2667 characters), 8 (3279), and 9 (2216). The retained candidate already extracted these three arguments, but its report incorrectly described the earlier zero-new-node delivery and defended keeping the long steps. This report supersedes that assessment. Each extracted node now carries a statement only, has the required searches, and is cited by its corresponding short step. None of the ten revised steps exceeds 2000 characters.

The mathematical comparison follows the Q60 route note. Step 6 proves the relative nerve's horn, fiber and strict transport formulas; it does not identify the coherent classifying functor. Step 7 uses the existing unmarked cone comparison, with its specified natural map on every simplicial X. Step 8 uses the actual derived model comparison through target change and enriched evaluation. Step 9 removes the valuewise opposite through a natural strict singular-realization zigzag. Step 10 applies these comparisons to the explicit counit. The rejected inference from strict transport alone is not restored, nor are the parent's classification clause or the Cat-infinity analogue used.

During this audit I clarified that the displayed replacement unit and counit in the new replacement lemma are maps in the localized categories, with replacement equivalences inverted. I introduced its notation L_B explicitly, clarified that restriction compatibility is derived and coherent, repaired a missing TeX backslash in the opposite lemma, and replaced the new citations' introductory quotations by their actual comparison conclusions. Invalid historical Loogle identifier queries are retained as invalid queries, and are supplemented by valid searches. They are not evidence of absence.

The item's full statement, including every quantifier, the arbitrary-simplicial-input adjunction, the Kan counit without a projective-cofibrancy assumption, and the coherent ordinary-base comparison, is unchanged. Its Lean record is byte-for-byte equal as JSON data to the current shared record. Existing maintainer-owned metadata is retained by the delivery tool.

## What remains unfinished

The three new nodes are independent statement-only stage-1 tasks. Their proofs are not certified by this split. The required fresh server preflight and push remain the delivery gates; no historical dry run is substituted for them.

## Not duplicates

lem-coef-covariant-derived-replacement-base-change vs lem-coef-model-infinity-derived-adjunction: the existing theorem constructs derived adjoints generally; the new lemma records the covariant cone replacement, its equivalence normalization, objectwise-Kan evaluation and coherent restriction compatibility.

lem-coef-covariant-derived-replacement-base-change vs lem-coef-simplicial-right-fibration-presentation: the presentation supplies the concrete adjunction and base-change isomorphisms; the new lemma states their coherent derived replacement comparison. It does not assert the relative-nerve formula of the item.

lem-coef-unmarked-cone-model-comparison vs lem-coef-unmarked-relative-nerve-cone-comparison: the existing node supplies the natural objectwise weak map H_C(X) to F_C(X)-op for every X; the new node compares the cone Quillen model after enriched left Kan extension along the coherent counit. It does not supply the explicit F_C quotient or the item's relative-nerve classification.

lem-coef-unmarked-cone-model-comparison vs lem-coef-unmarked-straightening-target-change: target change gives a strict isomorphism with no weak-equivalence hypotheses; the new statement includes cofibrancy, the DK counit, and the adjoint weak-equivalence criterion on that specific diagram.

lem-coef-strict-opposite-realization-zigzag vs lem-cbc-realization-singular-unit-weak: the existing node gives the unit for an individual simplicial set; the new statement compares opposite strict diagrams through a Kan intermediate and descends the resulting coherent equivalence to the original small-space functor category.

lem-coef-strict-opposite-realization-zigzag vs lem-coef-realization-finite-limits: the latter supplies the realization/singular adjunction and horn geometry; it does not state the barycentric-reversal zigzag, its coherent naturality or the universe descent.

Whole-DAG keyword and source-place searches and `tools/blueprint_refs.py search straightening` were read; the blueprint search finds zero blueprint straightening nodes. The existing unmarked cone comparison and target-change nodes are reused. All three new nodes retain the nearest blueprint ancestor `prop-coef-integral-exceptional-adjoint`, its exact proof-paragraph provenance and the complete via chain. The chapter and unit routes are retained, and no unit realization fields need modification.

## Review by Q42

I checked the retained proof against delivery-errors B–E and the numbered return. The three extracted technical statements introduce their own objects and hypotheses, carry no proof or proof dependencies, and have genuine logged Mathlib searches. I read the source comparison and evaluation places above and the complete directly cited statements. The following is the mathematical review of the actual revised proof, rather than a defence of its historical long steps.

1. The replacement lemma supplies coherent derived units, counits and restriction compatibility for the actual covariant cone adjunction. Model-nerve localization identifies the simplicial bifibrant model with its localization. Rectification with the identity indexing map gives enriched evaluation into the full functor quasicategory. Transport-classification and coherent-nerve-comparison are used only for model and space conventions. An objectwise Kan diagram may be replaced by a cofibrant trivial fibration while retaining fibrancy. The new replacement statement specifies localized maps, so no nonexistent strict map to an unreplaced object is assumed.

2. The quotient calculation retains exactly a simplex of X and an arrow from its final vertex to c, giving X times over N(C) the nerve of C/c. Reducing a representative to the image of its monotone map preserves that arrow composed with the final segment. This also proves uniqueness, including repeated vertices and degeneracies. Postcomposition and the last-face action give precisely the two required functorialities. The cited diagram definition supplies the simplices and operators.

3. The adjunction is the explicit inverse correspondence: evaluate on the identity-arrow summand to extract each t_J, and apply G(h) to reconstruct every summand. Its compatibility is exactly the quotient relation. Image and restriction of subsets commute with simplex operators. This uses no Kan assumption.

4. The counit has an explicit section and simplicial homotopy, with the mixed-subset formula compatible because h_j composed with the segment i to j is h_i. The realization testing criterion cited here applies to arbitrary simplicial sources and targets, so the conclusion does not assume the strict diagram is projectively cofibrant.

5. The relative-cylinder lemma applies to the pullback left fibration over N(C/c), with E as cylinder domain and X_c as fixed subset. The terminal-arrow homotopy fixes id_c; consequently its prescribed lift on X_c is compatible. Its endpoint is a retraction, giving the claimed weak equivalence by the cited realization criterion. No natural family of choices of contractions in c is asserted.

6. The missing left-horn face has index i less than r, so both unspecified subsets end at r. Transport into D(sigma(r)) turns the given data into one Kan horn; a filler supplies both missing maps. This includes r=1,i=0. A constant base string has fiber D(c). The strict transport formulas retain units and composition, and no coherent-classification inference is drawn here.

7. The existing unmarked comparison node states the exact natural map alpha from the ordered-cone pushout H_C(X) to F_C(X)-op for every simplicial X over N(C). Its conclusion is objectwise weak equivalence, with no fibrancy requirement. Its minimum-subset prescription descends through the actual cube quotient; the step does not identify that quotient with the unquotiented cube. Thus its F_C is the comma pullback of step 2, and all hypotheses match.

8. The new model-comparison node separates the hidden model inference: the opposite counit is DK, P is projectively cofibrant because X-op is cofibrant in its slice and the cone functor is left Quillen, and target change identifies u_!P with H_C(X). Compose alpha with v-op to obtain w. Reversal of barycentric coordinates preserves weak homotopy equivalences, so w is objectwise weak. The enriched Kan-extension criterion and then the cone Quillen criterion give the comparison on unstraightenings. D-op is objectwise Kan, since opposite reverses horn indices. For enriched evaluation, replace the fibrant diagram by a cofibrant trivial fibration as in step 1, apply rectification's actual evaluation comparison, and invert the objectwise replacement equivalence. This identifies all Q_r coherences, rather than only fibers or edges. No cofibrancy assumption is added to D.

9. The new opposite-zigzag lemma supplies the strict natural diagram D-op to Sing|D| from D. Its first arrow is the characteristic-map unit for D-op followed by the singular image of barycentric reversal, and the second is the unit for D. The unit node supplies weak equivalence; reversal is a homeomorphism by reversing coordinates twice. The realization horn retraction proves that the singular intermediate is Kan. Both arrows commute with strict diagram maps. The pointwise equivalence criterion upgrades this to coherent equivalence; the full small-space subcategory contains the resulting equivalence and its witnesses between the two small endpoints. Thus no enlarged coefficient category replaces the item's fixed space category.

10. Apply steps 7–9 with X=R_CD and v equal to the counit. Steps 4 and 6 supply exactly its weak-equivalence and left-fibration hypotheses. For a general v, the fiber map of its adjoint is the composite v_c i_c; step 5 and the stated fiberwise criterion make it an equivalence. Actual adjunction maps, alpha, derived units/counits, enriched evaluation and the strict singular zigzag supply the stated coherent naturality. Neither a transport recognition rule nor a classification theorem depending on this item is used.

I tested empty C, empty X, terminal C, the base [1], constant and repeated strings, and empty Kan fibers. At terminal C the quotient left adjoint and relative nerve reduce to the identity; the model comparison reduces to its ordinary cone Quillen criterion. On [1], barycentric reversal accounts for the necessary valuewise opposite. On [2], the quotient identifies the vertices {0,2} and {0,1,2}, whose minima agree; this checks descent of the comparison map without the false unquotiented-cube identification. Replacement formulas are interpreted after localization even for noncofibrant diagrams. No change of the item's statement is needed.

A fresh traversal of all statement and proof prerequisites of the overlaid item found no missing dependency and no cycle. In particular the full closures of the cone comparison, both presentation nodes and all three new inputs do not return to this item. The historical cycle and closure counts are not substituted for this traversal. All non-elementary steps are shorter than 2000 characters; the hidden arguments in the three specifically returned steps are now named technical inputs. The remaining checked quotient, adjunction, counit, cylinder and horn arguments are retained.

Mathlib searches are reused from `searches.jsonl` after reading their recorded outputs. Each new node has its own concept query, Loogle query, grep and LeanSearch query, supplemented by a second semantic phrasing and valid Loogle queries. The invalid unresolved-identifier Loogle queries are labelled invalid, never used to establish absence. Valid Loogle finds ordinary left-extension constructions, opposite-simplicial-set operators, and injective model structures on cochain complexes; these do not state the technical comparisons here. The semantic hits likewise concern ordinary nerve adjunctions, enriched nerve definitions or ordinary categorical equivalences. No search was invented and no unavailable service is called a negative result.
