# Q26 stage-1 report

1. Files written: `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-strict-henselization-residue-automorphism-lift.json` (statement, now split; no exact Mathlib match). Supporting files: `citations.json` and this report. No new nodes; no new Mathlib leaves.
2. Attachments: none. The project-source searches by blueprint tag and by strict-henselization/residue-automorphism terminology found no declaration stating the whole item. `BoundaryStalk.lean` discusses the action of decomposition-group elements, not the required converse lifting construction. No Lean was written or compiled.
3. WANTED: none.
4. The item had no proof. Its statement is retained verbatim. The short automorphism assertion in Stacks 0BSW needed its finite-stage restrictions, uniqueness, transition compatibility, colimit inverse and residue calculation written out. This split does so, and keeps the extension to the fraction-field separable closure separate from the ring construction. No statement dispute or unit-route error was found.
5. Unfinished: none at this one-level split. Existing unsplit dependencies remain their own items.

## Sources and searches

I read `pione.tex`, Tag 0BSW (`lemma-identify-inertia`), especially the paragraph beginning with automorphisms over the henselization; `algebra.tex`, Tag 0BSL (`remark-construct-sh-from-h`) in full and Tag 04GK (`lemma-henselian-cat-finite-etale`) including its full-faithfulness argument; and `fields.tex`, Tag 0BME (`lemma-lift-maps`), statement and proof. The finite-stage assembly follows those sources rather than the inertia fixed-ring theorem, which is not needed here.

I read the chapter/unit records and the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`. The current last paragraph retains the unramified-at-infinity/inertia equivalence for which this technical item was created. The old unit has no proof steps to replace. Its source snapshot differs from the latest path, but no new mathematical route is introduced here.

DAG searches for 04GK/0BSL and for automorphisms extending through fraction fields located existing generic tools. Whole-blueprint searches were run for `automorphism`, `henselian finite`, `separable closure` and `strict henselization`; none states this item's finite-stage lifting comparison. The broad automorphism query was empty. I reused existing nodes instead of creating special cases. In particular, `lem-sfb-normal-intermediate-isomorphism-lifts` already covers the final extension without requiring the intermediate extension to be normal.

The actual new searches are in `searches.jsonl` and were added without altering the inherited searches. Both LeanFinder phrasings, LeanSearch, Loogle and Mathlib grep were read. Two Loogle patterns contained unknown identifiers; these are explicitly recorded as unavailable, and a valid `HenselianLocalRing, "ResidueField"` search was then run. One grep selected the nonexistent subdirectory `RingTheory/Henselian` rather than the file `RingTheory/Henselian.lean`; its empty result is recorded as inconclusive, and the later `RingTheory` search includes that file. I inspected `Henselian.lean` lines 108–165: root lifting is not finite-etale full faithfulness. I also read `IntegralClosure/IntegralRestrict.lean` around `galLift` and `galLiftEquiv`: these require integral-closure data and do not provide the residue comparison. `FieldTheory/Normal/Basic.lean` lines 181–222 directly supports the reused Mathlib leaf for the last step. Thus the item itself is not a Mathlib leaf.

## Not duplicates

No new nodes were created. Existing tools were cited, including the stronger intermediate-isomorphism extension leaf; no finite-stage automorphism node or colimit-automorphism node duplicates a clause of the item.

## Review by Q26

I checked delivery-errors B through E, including the repeated sections, against the written proof and sources. There are no statement-only new nodes needing their own source or edge-case checks. All eight step/node citations in `citations.json` are verbatim statements read from their files. I checked the content, not merely whether the quote is a substring.

Step 1 uses the defining universal property in `def-weil-pbc-henselization-at-prime`: the identity of the already henselian ring H has that property, so `lem-wf-strict-henselization-finite-lifts` applies with A=H. The latter statement expressly gives the finite local etale diagram, its residue-compatible strict-henselization identification, and the restriction to finite Galois residue extensions. This avoids applying a construction over an arbitrary local base without accounting for its henselization. Its finite Galois clause also supplies the normality used in step 2. Step 2 writes the root argument for both tau and its inverse, so restriction to e is justified even for a nonperfect residue field; no unstated invariance of a merely separable nonnormal subfield is assumed.

Step 3 uses exactly the Hom-set bijection of `lem-weil-pbc-henselian-finite-etale-map-bijective`, with base H and finite etale source/target B_e or B_f. The quotient in that node is the same residue algebra B_e/m_H B_e identified with e by the finite-lift statement. Lifts of the inverse residue automorphism prove invertibility by injectivity of that bijection. The two composites for every transition have explicitly the same residue map, so compatibility follows from the same cited statement. I do not use full faithfulness for a target equal to the infinite ring R.

Step 4 uses only the colimit universal property as explicitly stated in `def-weil-pbc-category-colimit` and the residue-compatible colimit assertion of `lem-wf-strict-henselization-finite-lifts`. The index is a set of finite subfields of a fixed field, hence small, and it is the filtered Galois index already allowed by the latter node. Both inverse equations and the residue identity are checked on every coprojection and then follow by colimit uniqueness. This argument does not rely on unproved injectivity of coprojections or an identification of an arbitrary colimit with a literal union. The residue calculation proves reduction to tau on the whole residue field, rather than merely on an unspecified finite field.

Step 5 writes the fraction formula, its independence of representatives by cross multiplication, its inverse, and the same formula for the given embedding into Omega. The domain and injectivity assumptions are precisely those already in the item; no normality of R is added. Since t fixes H it fixes F. These are elementary computations with fractions, not another independent lifting theorem.

Step 6 uses the statement of `lem-weil-pbc-separable-closure-exists-galois` (2), with the bottom intermediate field F, to obtain algebraicity and normality of Omega/F. The statement of `lem-sfb-normal-intermediate-isomorphism-lifts` requires only those ambient hypotheses and an F-isomorphism of intermediate subfields. Take both subfields to be the embedded fraction field L and conjugate t_L by its specified embedding. The statement gives exactly the restriction equation for u. Neither normality nor finite degree of L/F is assumed or silently proved. These two nodes are existing Mathlib leaves.

I tested the statement on H a field (R is its separable closure and the construction restricts tau), on separably closed residue field (the residue Galois group is trivial), on the finite stage e=kappa and on tau=1 (unique lifts and both colimit maps are identities), and on imperfect residue fields in positive characteristic. The proof uses finite separable normal stages, so no perfectness, Noetherian, completeness, or excellence hypothesis is smuggled in. The inverse-composite calculation also tests the order of composition. No proof step exceeds 2000 characters, and no hidden standard comparison was moved into prose: the non-elementary facts all have cited theorem nodes. No SGA source is used.

The two generic off-unit tools are declared in `split_report.tool_uses`: the finite-lift colimit construction (already a statement dependency) and the Hom-set reduction bijection. They implement the local-ring argument of 0BSW; they do not replace a unit proof step, since this conventions unit has none. The definition of henselization and of colimit are notions, and the two field-extension nodes are Mathlib tools.

## Validation

The required server dry run and delivery are run after this report is written. No local DAG/preflight checker and no compiler or Lake command is run.
