1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-unbounded-derived-functor-cohomological-bound.json`: item split, one proof step, no Mathlib match.
   - `citations.json`: verbatim citations for the five item steps.
2. Attachments: none.
3. WANTED: `literature/stacks-project/perfect.tex`, Tag 08D4, for the item and the new stabilization node. The local repository carries the citation metadata but not the Stacks source tree; I read `/home/ubuntu/c1-stacks-review/perfect.tex`.
4. The item was unsplit. Its source proof uses the upper-truncation clause (2) of Tag 08D4; I kept that clause inside the item's five proof steps rather than introducing a node that would restate part of the item. No statement was weakened.
5. What I could not finish: no Lean declaration or Mathlib theorem states this scheme-theoretic unbounded derived-functor result.

## Review by M1

I checked the item against Tag 08D4, part (3), and read its complete proof in `perfect.tex` (the source is available at `/home/ubuntu/c1-stacks-review/perfect.tex`, lines 158--230). The item introduces the free integer `b` and all hypotheses listed in the source.

Steps 1--4 reproduce the source's truncation-limit, Milnor exact sequence, shifted truncation triangle, and Mittag--Leffler stabilization arguments; I checked each cited definition says the derived category, derived functors, or standard truncation used there. Step 5 applies the stabilization with `b' = b+N`; `τ_{≥ b+1}E=0` follows from the stated cohomology bound, and the integer inequality gives exactly `i>b+N-1`. This is the final paragraph of the source proof, with the index calculation written explicitly.

I searched the whole DAG for Tag 08D4, truncation-stabilization keywords, and related derived-limit statements, and searched the full blueprint; no additional node was created because the stabilization clause is part of the item's proof. I ran LeanFinder, Loogle, grep, and LeanSearch (the latter was unavailable) for the item. The Mathlib hits were only generic derived-category truncation declarations, so the item is not a Mathlib leaf. I tested the index on `N=0`, `N=1`, and the zero complex: the conclusion and truncation indices remain correct. No duplicate or cycle is introduced.

## Second reading by M1

Item statement: checked against perfect.tex Tag 08D4, lemma-application-nice-K-injective, hypotheses (1)--(2) and clause (3); the additive/product and quasi-coherent vanishing assumptions and the index `i>b+N-1` agree. Zero complex, `N=0`, `N=1`, and a field scheme give the expected vacuous or ordinary bounds.

Step 1: checked against the Tag 08D4 truncation reconstruction and RF/Rlim comparison; repaired by citing the new self-contained truncation-tower node.

Step 2: checked against the displayed Milnor sequence in Tag 08D4 and More on Algebra Tag 07KY; repaired by citing the new Milnor-sequence node.

Step 3: checked the shifted truncation triangle and both endpoint indices against Tag 08D4; repaired by citing the new stabilization node, which states the exact isomorphism range.

Step 4: checked eventual constancy, Mittag--Leffler, and the index `N-i-1` against the source conclusion; repaired by citing the stabilization node rather than definitions alone.

Step 5: checked the upper truncation `tau_{>=b+1} E=0` and the substitution `c=b` against Tag 08D4 part (3); rewrote the final inequality explicitly.

New node `lem-pc-qcoh-truncation-derived-limit`: statement-only, self-contained definitions, source Tag 08D4/08D3/08D1, Mathlib searches recorded; no existing node states this scheme-theoretic fact.

New node `lem-pc-derived-limit-milnor-sequence`: statement-only, self-contained derived-limit and cohomology notions, source Tag 08D4/07KY, Mathlib searches recorded; no existing node states the abelian-group Milnor sequence.

New node `lem-pc-derived-functor-truncation-stabilization`: statement-only, source Tag 08D4 parts (2)--(3), Mathlib searches recorded; it is the strict intermediate stabilization fact, not a restatement of the item.

Changes: added the three necessary dependency nodes, replaced uncited derived-limit assertions with node citations, and corrected the final bound application.

## Not duplicates

`lem-pc-qcoh-truncation-derived-limit` vs `lem-pc-unbounded-derived-functor-cohomological-bound`: reconstruction and RF/Rlim compatibility are prerequisites; it does not assert any cohomological vanishing bound.

`lem-pc-qcoh-truncation-derived-limit` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the new node is for arbitrary additive functors on scheme modules and truncation towers, while the existing node is a pushforward-specific acyclicity result.

`lem-pc-qcoh-truncation-derived-limit` vs `lem-sc-qcoh-acyclic-derived-sections-comparison`: the new node is the unbounded derived-limit reconstruction; the existing node compares derived sections and pushforward for a specific morphism.

`lem-pc-derived-limit-milnor-sequence` vs `lem-pc-unbounded-derived-functor-cohomological-bound`: the new node is the generic Milnor short exact sequence for any countable tower in `D(Ab)`, not the item's vanishing conclusion.

`lem-pc-derived-limit-milnor-sequence` vs `lem-weil-pbc-mittag-leffler`: the existing node treats finite abelian-group towers in a pro-etale setting; the new node treats arbitrary countable towers in `D(Ab)`.

`lem-pc-derived-limit-milnor-sequence` vs `prop-weil-pbc-roos-triangle`: the existing proposition defines the Roos triangle, while the new node gives its cohomology exact sequence and the `R^1 lim` term.

`lem-pc-derived-limit-milnor-sequence` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the new node is a general derived-limit calculation, not a pushforward acyclicity statement.

`lem-pc-derived-limit-milnor-sequence` vs `lem-sc-qcoh-acyclic-derived-sections-comparison`: the new node is independent of scheme morphisms and section/pushforward comparisons.

`lem-pc-derived-functor-truncation-stabilization` vs `lem-pc-unbounded-derived-functor-cohomological-bound`: the new node is the fixed-degree tower stabilization intermediate; the item is the final upper-bound theorem for bounded-above `E`.

`lem-pc-derived-functor-truncation-stabilization` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the new node concerns an arbitrary additive derived functor and truncation tower, not derived pushforward acyclicity.

`lem-pc-derived-functor-truncation-stabilization` vs `lem-sc-qcoh-acyclic-derived-sections-comparison`: the new node supplies the index stabilization and vanishing calculation; the existing node is a comparison theorem for sections.
