# Worker report: lem-coef-segal-dk-two-out-of-six

## Files written

- `dag/nodes/sec-six-functors/lem-coef-segal-dk-two-out-of-six.json`: existing statement, split into nine steps; five existing proof dependencies. Statement and statement dependencies unchanged. Mathlib verdict: no match.
- `citations.json`: a verbatim statement quotation for every proof-step citation.
- No new nodes; no Mathlib leaves. The sandbox also retains the search log and the script that wrote the JSON; these are not DAG delivery files.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, `twoOutOfSix`, `two.out.of.six`, `Segal`, and `Dwyer.?Kan` found no project declaration stating this item. The upstream master source was also searched for the exact tag and cancellation names, with no result. No Lean file was written and no compiler was run.

## Sources and WANTED

WANTED: Charles Rezk, *A model for the homotopy theory of homotopy theory*, Sections 4.1, 5.1, 5.3–5.5, 7.4 and Lemma 7.5, printed pp.11–13 and 16, for lem-coef-segal-dk-two-out-of-six. The document is not archived in `literature/`. I read the PDF online at the URL already recorded in the node, without downloading or writing it into the repository. Lemma 7.5 states exactly both clauses, without completeness. Its proof is omitted as “Straightforward”; the missing argument is supplied here, with `proof_origin.by = agent`.

I read the chapter record `sec-six-functors`, the unit `sk-prop-sf-biduality-general`, and the ancestor `prop-coef-integral-exceptional-adjoint`, particularly the second proof paragraph's derived-coefficient adjunction display. This item is generic mapping-space infrastructure below that paragraph, through the Rezk chain already recorded in its `blueprint.from.via`; it is not a new claim that the blueprint explicitly states Segal cancellation. The source is Rezk, not SGA. No Stacks tag states this theorem, so no unrelated tag is assigned to it.

## Faults and corrections

There is no statement dispute or changed hypothesis. The item arrived with an empty proof. Its two conclusions are both retained, including cancellation for noncomplete Segal spaces.

The main issue to avoid is canceling the mapping-space maps only on pairs in the image of `a`, and declaring the entire map `b` fully faithful. Step 8 explicitly extends that result by essential surjectivity of `ha` and conjugation. Step 9 similarly extends the result for `c` from pairs in the image of `b`. Neither extension uses surjectivity on the components of the object spaces; isomorphisms in the homotopy categories are what is available.

I avoided adding a separate cancellation node that would merely restate a clause of the item, and avoided adding elementary generic two-out-of-six nodes. The small quasi-inverse arguments for ordinary categories and Kan spaces are written into the proof. The parameterized composition argument is also written out, rather than citing a statement about fully faithful Yoneda embeddings or about pointwise compositions that would not give homotopies of entire mapping-space maps.

Initially the shared snapshot did not contain the assigned file; it appeared during the normal snapshot refresh. Work proceeded from that file. The early no-files check was superseded by the completed sandbox.

## Not duplicates

No new nodes are proposed. I searched the whole DAG by Segal, Dwyer–Kan, two-out-of-six, mapping-space composition and conjugation terminology. The existing `lem-coef-segal-categorical-equivalence-dk` concerns a categorical homotopy inverse, not two-out-of-six. Its statement cannot be used to cancel arbitrary composites. The explicit Rezk completion and Segal-diagonal results are downstream consumers and are not used. `lem-cbc-kan-whitehead-inverse` already states the generic inverse theorem needed for the Kan-space calculation, so it is reused.

Whole-blueprint searches `blueprint_refs.py search 'Dwyer'`, `search 'Segal'`, and `search 'two-out-of-six'` found no blueprint statement of this item. The ancestor command confirms `prop-coef-integral-exceptional-adjoint`; `same_as` remains empty.

## Mathlib searches

All five searches recorded in the item were actually run with `msearch.py Q28 lem-coef-segal-dk-two-out-of-six`: two different LeanFinder phrasings, Loogle, grep under `AlgebraicTopology`, and LeanSearch (five calls in total). All services answered. The grep returns `StrictSegal.spineEquiv` comments at lines 124 and 313. I read `StrictSegal.lean:115–134,275–325`: these are equivalences between simplices and spines inside a strict Segal simplicial set, not Dwyer–Kan equivalences between simplicial spaces. The second semantic phrasing also returned generic homotopy-class bijectivity, coskeleton full faithfulness and the nerve's full faithfulness; none states the item. The exact queries and actual returned summaries, including tool, subdirectory, hit count and top names, are preserved from `searches.jsonl` in `mathlib_searches`. No search was invented and no unavailable service was called a negative result.

## Review by Q28

I read Rezk 4.1 and 5.1 against the definitions in the item: Reedy fibrancy, strict mapping fibers, consecutive-edge Segal maps, and the homotopy category all match. In 7.4 and 7.5 the two Dwyer–Kan conditions and both cancellation conclusions match exactly; no completeness, connectedness or object-surjectivity hypothesis is supplied by the source or added here. There are no new-node statements to review.

For step 1 I opened `lem-coef-kan-quillen-right-proper` and `lem-coef-reedy-model-structure`: the former gives precisely the realization-defined weak equivalences, and the latter explicitly states the two-out-of-three axiom for a model category. The mapping map of a composite is literally the composite on strict fibers. Quasi-inverses in the ordinary categories compose in reverse order.

For step 2 those same statements give Kan horn lifting for the matching maps and boundary lifting for trivial fibrations. I checked the finite face-attachment argument: subobjects of the representable are unions of faces, and attaching in increasing dimension ensures each boundary is already present. Pullback and successive horn lifts prove the fibration claim, including degree zero. The fixed-vertex Segal comparison is a pullback of the whole Segal map. Its sections and its homotopies over an arbitrary parameter space are constructed by the stated boundary-cell property. Thus no unstated theorem that arbitrary realization preserves pullbacks is used.

Step 3 is the explicit use of that lifting property, cited again to the Kan node. I checked all four faces of the chosen 3-simplex and the identity `d₁d₁ = d₁d₂`. The comparison is parameterized by the full product of mapping spaces; it is not just a relation on their components. Degeneracies give both units. The two candidate lifts in the target of a Segal-space map have the same ordered pair of edges, so the naturality homotopy has the required endpoints.

In step 4 I opened both `lem-coef-simplicial-realization-cylinder` and `lem-coef-homotopy-groups-basepoint-change`. The first provides an ordinary-product cylinder homeomorphism, with both endpoints fixed as used. The second says exactly that continuous homotopies preserve the weak-equivalence property, and that a homotopy equivalence induces all based-group isomorphisms even when its homotopies move basepoints. I checked the inverse conjugation formula and the order of all four arrows. Paths representing the inverse equations occur in the relevant mapping spaces, not just in the total arrow space. Only finite chains of homotopies are concatenated after realization.

For step 5 I read the entire statement of `lem-cbc-kan-whitehead-inverse`: all its hypotheses apply because the four inputs are Kan and the two composites are weak homotopy equivalences. It supplies actual simplicial maps and both homotopies, not merely an inverse in an unspecified localization. I checked the types `l = sw : Z → Y`, `t = ur : Z → Y`, the equations `lv ≃ 1`, `vt ≃ 1`, and `l ≃ lvt ≃ t`; thus `t` is a two-sided inverse up to realized homotopy. The cylinder, basepoint and two-out-of-three statements cited there say exactly what is used. This off-unit Whitehead result is declared as a generic tool use in `split_report.tool_uses`.

Step 6 is elementary quasi-inverse algebra, not a new theorem applied without citation: `P = RH` is a left inverse and `Q = FL` a right inverse for `G`; `P ≅ PGQ ≅ Q` gives both equations for `Q`. I checked the source and target categories of each composition and natural isomorphism.

In step 7 the two adjacent composites are at the exact pairs required by the hypotheses: `ba` at `(x,y)`, and `cb` at `(ax,ay)`. It invokes the already-expanded step-5 calculation; the cited Whitehead statement supplies its only inverse-existence input. Steps 8 and 9 use the homotopy-invariance and two-out-of-three statements already read, together with the conjugation maps and squares actually constructed in steps 2–4. In step 8 `ha` is essentially surjective by step 6; in step 9 it is `hb`. Each pair of lifts is chosen separately, and no uniform or coherent choice over the object space is required for a fully faithful mapping-space test.

I tested the argument on empty Segal spaces, a point, discrete nerves of categories with isomorphic but distinct objects, an ordinary category with a noninvertible arrow, and one-object Segal groupoids with nontrivial higher mapping spaces. The latter checks why a mere bijection on hom-sets would be insufficient. Empty mapping spaces are permitted by both Kan nodes. In the all-empty case every pair assertion is vacuous; when an equivalence has empty source its target homotopy category must also be empty, so essential surjectivity is still valid. The noncomplete walking-isomorphism nerve is allowed throughout, as the statement requires.

Against delivery-errors B–E: no new definitions or statement-only lemmas were manufactured, the existing statement is self-contained, TeX is preserved, and no spurious Stacks citation or Mathlib leaf is asserted. Every non-elementary input is a quoted existing statement; no proof of a cited node is used as if it were its statement. The proof carries the argument instead of moving a conclusion into a new node. All source/target objects and hypotheses above were checked explicitly. I verified that no chosen proof dependency reaches this item, so the completion chain is not made circular. I corrected the draft's search-count wording to the actual log before handing over. Only the required remote checks are run; there is no local DAG-check execution or Lean compilation.

## Unfinished work

No mathematical step is left open. Independent second reading and delivery belong to the next worker. The READY handoff is issued only after the required delivery dry run prints OK.

## Second reading by Q28

I checked the item statement against Rezk Sections 7.4 and Lemma 7.5, including both composition and cancellation clauses, and found all hypotheses and the absence of completeness unchanged. Step 1 was checked against the cited Kan model and Reedy two-out-of-three statements; its strict-fiber composite and categorical quasi-inverse argument are correctly stated. Step 2 was checked against the Reedy matching-map and Kan lifting statements; the parameterized boundary-cell construction and Kan fiber claims are explicit. Step 3 was checked against the same Kan lifting statement and the Segal composition definitions; the face identities, units, and naturality parameter are supplied. Step 4 was checked against the realization-cylinder and basepoint-change statements; conjugation and nonstationary-basepoint homotopy invariance are used with the right directions. Step 5 was checked against the full Kan Whitehead inverse statement and realization/basepoint nodes; the types of the constructed inverse maps and two-out-of-three applications match. Step 6 is elementary quasi-inverse algebra with all compositions typed. Step 7 applies the Kan cancellation argument at the exact image pairs and all four mapping spaces are Kan by step 2. Step 8 uses essential surjectivity of the homotopy-category functor and the step-4 conjugation square to extend full faithfulness of b to arbitrary pairs. Step 9 similarly extends c using essential surjectivity of hb and applies Kan two-out-of-three. I tested empty Segal spaces, a point, discrete nerves, a walking noninvertible arrow, and a one-object Segal groupoid with nontrivial mapping space; no edge case adds a hypothesis.

There are no new nodes to review: the split uses only existing dependencies, so B1--B7 and duplicate-node checks are vacuous. I verified every proof citation has a verbatim statement quotation in citations.json and that no step relies on a cited proof. I corrected the node metadata `created.item` from the unrelated categorical-equivalence item to `lem-coef-segal-dk-two-out-of-six`; this was the only file correction. The split report and citation/search logs remain otherwise unchanged.
