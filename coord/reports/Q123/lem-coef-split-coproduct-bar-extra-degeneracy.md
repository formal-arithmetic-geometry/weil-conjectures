# Stage-1 delivery: lem-coef-split-coproduct-bar-extra-degeneracy

Group Q123; direct delivery; 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-split-coproduct-bar-extra-degeneracy.json`: existing statement node, now split into seven explicit elementary steps; no exact Mathlib match for the coproduct-bar assertion. Statement and statement dependencies retained exactly.
- `citations.json`: five step/node citations, each quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. Neither chapter nor unit records were edited.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id and for extra degeneracy, fixed-object categories, coproduct bar, split coproduct, and unused factor found no declaration stating this assertion. The upstream master is not used as evidence of a completed proof.

## WANTED

WANTED: Dwyer--Kan, *Simplicial localizations of categories*, Proposition 8.2, printed pp.278-279, for lem-coef-split-coproduct-bar-extra-degeneracy; archive the PDF locally under `literature/`. This paper is absent from this machine's literature directory and LIST.md. I read the supplied [Rochester PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf) with the browser, particularly section 1.4(ii)-(iii) and the proof on printed p.279, without downloading a file. It provides context for the split bar but omits the explicit calculation. The complete proof delivered here is marked `proof_origin.by = agent`.

## Problems found and corrections

The item statement is correct as written; no STATEMENT-DISPUTED finding and no hypothesis or conclusion change. Its proof was empty. The source leaves the contraction implicit, so citing the proposition would not supply a split: I wrote the factor maps and their full index calculation.

The terminal-face boundary is essential: a factor that passes beyond the last copy is sent into $V$ by $v$, rather than discarded. Step 4 proves $d_1h_0=h_{-1}\varepsilon_0$ explicitly, and step 5 separates the last face from the internal folds. No unique reduced-word or free-factor assertion is used; arbitrary relations inside all three categories are respected.

The item's historical unit and ancestry are preserved. I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, and both the historical master and current main-20261015 files for `prop-coef-integral-exceptional-adjoint`. The current snapshot locates the ancestor under `sk-thm-sf-package` and gives its statement without a proof; the historical file contains the paragraph cited by the inherited ancestry. This delivery concerns only the existing lower-level split-bar input to step 6 of `lem-coef-fixed-object-scat-left-proper`, not a replacement route for the unit's coefficient adjunction or biduality.

## Mathlib and duplicate searches

The inherited Q80 Mathlib records are retained, and six actual Q123 searches are appended from `searches.jsonl`: LeanFinder twice with different phrasings, Loogle once, LeanSearch once, grep in AlgebraicTopology, and grep across Mathlib. All services answered; none is recorded as unavailable. I read each returned list. Relevant candidate sources read were `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:72-83,332-380` and `Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean:50-100`. The former defines generic extra-degeneracy data and a split-epimorphism Cech-nerve construction; the latter transfers that Cech construction to formal coproducts. Neither constructs the labelled coproduct powers in the item. The generic structure is already represented by `lem-coef-extra-degeneracy-contraction`; it is reused rather than recreated. The second LeanFinder wording returned monoidal and augmented-simplex-category declarations, none stating this bar assertion. Grep's second phrasing found no coproduct-bar construction.

`tools/blueprint_refs.py ancestor` confirmed `prop-coef-integral-exceptional-adjoint`; its searches for `coproduct bar` and `extra degeneracy` found zero blueprint nodes. I also read the parent left-properness node and searched the DAG for fixed-object/category/coproduct/word concepts. No new node is needed: the functoriality and index comparisons are short explicit calculations from the quotient-word construction already stated in the item.

## Not duplicates

There are no new nodes and hence no new/existing duplicate pairs. The existing generic extra-degeneracy result and the existing category and simplicial-set definitions are cited.

## Review by Q123

I checked delivery-errors B--E against the item and the cited node statements. For the item I read the Dwyer--Kan source as described above and the Mathlib extra-degeneracy fields. For the two basic definitions I read Stacks `categories.tex`, `definition-category`, Tag 0014, and `simplicial.tex`, `definition-simplicial-object`, Tag 016A, `section-simplicial-set`, Tag 0174, and `definition-terminology-simplicial-sets`, Tag 0175, checking the tag-to-label map. For the extra-degeneracy criterion I read the existing node's entire statement and its Mathlib structure source. No SGA source was used. There are no new-node sources to review.

Step 1 uses `def-nagata-category` for the identity and composition laws. It gives the word-level proof that the given factor functors respect every generating relation, and proves equality of functors from equality on factors; this is a direct consequence of the quotient construction in the statement, not an uncited normal-form theorem. Smallness follows because finite words in a set and their quotient are sets. The only hypotheses used are small categories with the same small object set and identity-on-objects factor maps.

Step 2 uses `def-weil-pbc-simplicial-set` precisely for its contravariant functor convention. The explicit minimum-index formula builds every operator. Its functor-law proof checks the equivalence of two inequalities and the empty case; it does not invoke an uncited simplicial-generators theorem. The convention at infinity means apply $v$ once and then fix $V$, so no identity or composition property beyond $v$ being a functor is assumed.

Step 3 uses the same definition's actual injection/surjection face and degeneracy conventions, quoted in citations.json. Computing the minimum for an omission or repetition gives the maps in the statement. The factor-by-factor augmentation equality is written out and proves naturality to the constant category.

Step 4 cites no external statement: by step 1 it suffices to compare the restrictions on $F$, $V$, and each $A_k$. It constructs the $h$ functors and checks each of the three low-degree identities, including the single-copy boundary. Step 5 checks the two ranges of face indices, with the last face applying $v$ and every other factor's target stated explicitly. Step 6 checks the two ranges $k\leq i$ and $k>i$ for the degeneracy identity. These two steps are arithmetic on labels, not separate comparison lemmas hidden inside a proof.

Step 7 uses `def-weil-pbc-simplicial-set` for the simplicial set obtained by restricting the functors to a fixed hom-set, and `lem-coef-extra-degeneracy-contraction` only for its exact displayed criterion that these five equation families are extra-degeneracy data. The node explicitly states this criterion; the step does not use its proof or infer an unstated property from the definition. All of the criterion's hypotheses have been established: simplicial set, augmentation to a constant set, section in degree zero, and maps in every nonnegative degree. The same object set is what permits restriction to fixed $x,y$.

For small cases I checked $O=\varnothing$ (the hom-set conclusion is vacuous), all factors discrete (only identities), and one-object categories with relations, including a nontrivial group and a functor $v$ collapsing its arrows (the relation-respecting argument still applies). Empty individual hom-sets cause no choices or nonemptiness assumptions. As a separate finite arithmetic check I verified the ordinal-composition formula on 320925 cases in degrees through 4 and the shifted face/degeneracy formulas on 7105 cases through degree 20, plus $d_1h_0$. These finite checks supplement the general symbolic proof; they are not a Lean check.

Every step is marked elementary because its complete argument is word-quotient descent, a finite-order inequality, or equality on the displayed factors. No non-elementary theorem is being disguised as elementary, and no new node would do more than restate a proved step. Step lengths are 820, 1022, 785, 659, 618, 428, and 740 characters, so none triggers the 2000-character review threshold. All uses equal proof_deps as a union; citations were checked literally against the repository statements. Statements and sources of all three cited nodes were read. No cycles or new off-unit tool uses are introduced.

## Unfinished work

None in this one-level split. Stage 2, Lean writing, and compilation are outside this delivery. Server dry run and push results are recorded below after those commands exit.
