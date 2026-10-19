# Q33 stage-1 delivery: lem-trf-henselian-smooth-algebra-lifting

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-henselian-smooth-algebra-lifting.json` (statement, split; not a Mathlib leaf), `citations.json`, and this report. No new nodes and no new Mathlib leaves. `searches.jsonl` records five searches run by the authorized command.
2. Attachments: none. Searched the slopmaster2 project source for the exact blueprint tag and the henselian/smooth lifting notions; no project declaration states this arbitrary-pair lifting result. The master source is reference material only.
3. WANTED: none.
4. The imported statement is correct and unchanged. The original node had no proof. Its existing searches and provenance are retained. The proof now follows Stacks 0H74; the previously implicit compatibility of the retraction with the specified quotient section is written out. The smooth-ring versus smooth-scheme distinction is handled by the exact existing comparison statement. No statement dispute or unit-route change.
5. Unfinished work: none for the one-level split. Existing cited inputs remain in their present DAG states.

## Sources and searches

Read Stacks `more-algebra.tex`, Tag 0H74 (`lemma-lift-smooth-henselian`) in full: tensor base change, 07M7, henselian retraction, and composition. Read 07M7 (`lemma-lift-section-smooth-morphism`) statement and proof, 09XI (`lemma-characterize-henselian-pair`) statement, and 0A02 (`lemma-henselization`) final paragraph. Read `algebra.tex` 00T4 (`lemma-base-change-smooth`), `morphisms.tex` 01V6 (`lemma-smooth-characterize`), and `more-morphisms.tex` 02H6 (`lemma-smooth-formally-smooth`) to verify the affine convention. Checked the chapter, unit, current main-20261015 ancestor proof, and the parent polar-section node's actual use: it needs existence of a lift, not uniqueness, with (A,I) the maximal-ideal pair of the valuation ring.

The whole-DAG title/statement and source-label searches found existing nodes for all four non-elementary inputs. Blueprint searches for `henselian smooth algebra lifting`, `henselian`, `07M7`, and `smooth section` produced no blueprint statement equivalent to the item. No node was created. The matching existing 07M7 node is reused, rather than repackaging the item as an auxiliary lifting lemma.

The five new Mathlib searches are recorded exactly from `searches.jsonl`: two LeanFinder phrasings, one Loogle, one grep and one LeanSearch. Both semantic phrasings return formal smoothness lifting over nilpotent ideals or adic completions. I read the returned signatures and the actual declarations `Algebra.FormallySmooth.exists_lift` (Smooth/Basic.lean:126--128) and `exists_mkₐ_comp_eq_of_isAdicComplete` (Smooth/AdicCompletion.lean:94--96). The nilpotence and completeness hypotheses cannot be inferred from a henselian pair. Loogle and the henselian/smooth grep found no match.

## Not duplicates

No new nodes. The four existing inputs are reused as stated, so there are no new/existing-node pairs to distinguish.

## Review by Q33

I checked delivery-errors B--E against the actual item, all cited statements, and the Stacks sources. No new definition, new statement-only leaf, unsupported source, or hidden auxiliary lemma is present. Every step is shorter than 2000 characters. `citations.json` quotes each cited node's full statement verbatim; every use is supported by that statement rather than by its proof.

Step 1 uses exactly clause (1) of `lem-weil-pbc-smooth-ring-map-base-change-composition`: arbitrary base ring change R to A is allowed and gives A tensor_R S in the stated order. The formula for sigma is R-balanced because tau respects the R-structures; it preserves multiplication because both target maps land in a commutative ring. This is the tensor universal property, not an additional algebraization result.

Step 2 uses the right-to-left direction of `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. Its statement compares precisely the ring definition of smoothness used by the item with the scheme definition used by the 07M7 node. Thus no formal-smoothness-only or finite-presentation hypothesis is lost.

Step 3 uses `lem-weil-pbc-smooth-section-etale-lift` with base A, J=I, B=A tensor_R S and sigma. Its statement supplies both the etale map and the specific induced quotient isomorphism alpha, together with qj=alpha sigma. These are the exact objects subsequently used; no choice from the proof of that lemma is needed.

Step 4 uses `lem-weil-pbc-henselization-stage-map` with B=A, C=A-prime, target A, J=I and identity base map. Its quotient isomorphism hypothesis is alpha, the pair hypothesis is the item's original (A,I), and the ideal-containment condition is equality. Rings can be placed in one common universe. I use only existence; I do not claim the smooth lift unique. This source's generic single-stage retraction is exactly the retraction sentence of 0H74, not a use of a henselization construction in place of the unit's route.

Step 5 uses no additional theorem: the retraction sends the generators f(i)x of IA-prime into I; consequently its quotient map is alpha's inverse. Substituting qj=alpha sigma then computes the reduction of the composite on each s. This verifies the actual specified tau rather than merely producing an arbitrary section.

I tested I=0 (the original tau itself is a lift), A=0 (all maps reduce to the unique zero-target map), S=R (the structure map lifts), and S=R[x_1,...,x_n] (choosing lifts of coordinates agrees with the conclusion). For a henselian pair I=A forces A=0: apply the idempotent uniqueness condition to B=A, whose quotient is zero. Thus the unit ideal introduces no hidden exceptional nonzero case. No Noetherian, local, nilpotent or complete hypothesis was used, and no uniqueness conclusion was added.

The three off-unit tools are declared in `split_report.tool_uses`: the affine smoothness comparison, 07M7, and the single-stage henselian retraction. They are generic algebra inputs to the horizontal-point branch; they do not replace any step of the trace-formula unit. The fourth input is already a Mathlib leaf. No SGA source is cited.
