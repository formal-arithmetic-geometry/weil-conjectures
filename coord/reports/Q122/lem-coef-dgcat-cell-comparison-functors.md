## Worker report

### Files written

- `dag/nodes/sec-six-functors/lem-coef-dgcat-cell-comparison-functors.json`: item, statement; split into nine steps. Existing statement unchanged. No Mathlib match.
- `citations.json`: one entry for every step/node citation, copied verbatim from the corresponding statement.
- `searches.jsonl`: five actual searches from this resumed session; existing node searches were retained as inherited evidence.
- `report.md`: this report and the signed self-review.

### Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` source for the exact blueprint tag, dg-category terminology, formal-cone comparison and contraction terminology, and checked `dag/lean_names_upstream.json`. The results concern ordinary cochain cones, scheme-level comparison cocones and unrelated tensor comparisons. No project declaration gives the item. The item's audit also records state `none` for both branches.

### Wanted literature

WANTED: Gonçalo Tabuada, *Théorie homotopique des DG-catégories*, arXiv:0710.4303, Chapter 1, Proposition 1.7 (printed p. 27) and Lemma 1.10 (printed p. 29), local archive for lem-coef-dgcat-cell-comparison-functors. I read the available [primary PDF online](https://arxiv.org/pdf/0710.4303), including the proof passage introducing L_0, L_1, L_2, L_3 and constructing the two comparison functors. No document was downloaded or added to the repository. These dg-category facts have no corresponding Stacks tag. The proof remains explicitly `by: agent`, as the arbitrary closed-arrow case and sign-expanded argument are our construction.

### Problems found and changes

The node was statement-only, not a completed split. Its statement is consistent with the cited cone convention, including both minus signs in the matrix. No statement correction is needed. In particular the cone coordinates are graded maps and need not be closed: their nonzero differentials are essential to the calculation. The proof now gives those differentials, every attaching equation, the contraction matrix and the representable restriction explicitly. Nothing is moved into a new node. Neither the parent equivalence-cell lemma nor the sibling word-generation lemma is used; inverse-functor identities are the parent's separate task.

The historical blueprint ancestor `prop-coef-integral-exceptional-adjoint` has its finite mapping-complex calculation in proof paragraph 2 of the older source; I read that proof. In current `main-20261015` the ancestor has moved to `sk-thm-sf-package` and its file carries only the statement. I read that statement as well, kept the existing historical ancestry and item unit, and recorded exactly which comparison part of the parent this split realizes. This does not change a unit or chapter. The chapter and the recorded `sk-prop-sf-biduality-general` unit were read; this is a foundational algebraic calculation below their prescribed route.

### Unfinished work

No proof step of this item remains. The two previously existing construction nodes remain dependencies with their own recorded status. No Lean was written, no compiler or build was run, and no live project or launcher file was changed.

## New nodes

None: zero new nodes and zero Mathlib leaves. The existing free-cell and labelled formal-cone statements already supply the non-elementary constructions.

## Not duplicates

No new node was created. Whole-DAG and imported-blueprint searches by `cone contraction`, `dg functor`, `dg category` and `contract` found no imported equivalent. Inspected the existing free-cell, formal-cone and cone-word-normal-form statements. The last concerns generation and equality of functors, not construction of this item's two functors, and is unnecessary here.

## Mathlib searches

All five fresh queries are in `searches.jsonl` and appended verbatim to the item's `mathlib_searches`. Both semantic services succeeded. LeanFinder was tried with two different formulations; LeanSearch returned ordinary mapping-cone declarations. Loogle with `"EnrichedCategory", "MappingCone"` and source grep with `dg[Cc]at|DGCategory|dg.?functor|Kontsevich` returned no hits. I read Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean, especially lines 13–22 and 52–54, and Pretriangulated.lean, especially lines 98–106. Their mapping-cone and map-of-homotopy constructions are for complexes in a preadditive category; they do not give free dg-category extensions or functors with these prescribed generator values. They are not exact matches or one-line specializations. Earlier searches already in the item were preserved; they were not represented as fresh searches of this session.

## Review by Q122

I checked delivery-errors B–E with the item, both dependency statements, and the source passage open. The source is Tabuada's Chapter 1 Proposition 1.7 and the comparison part of Lemma 1.10, read online, and the inherited blueprint ancestry described above. The lemma's auxiliary enlarged category has the same representable/cone/adjoined-contraction pattern as our item. Its special auxiliary arrow is not needed for the comparison construction: every equation here uses only a closed degree-zero u. No cofibrancy, flatness, projectivity, or invertibility of u has been introduced.

For step 1, I read the statement of `lem-coef-dgcat-free-cell-calculus`: it gives free adjoining of an arrow with prescribed closed differential, unchanged objects, and the word differential. The two endomorphism attaching expressions are closed after v is added, and the expression for dw is closed after a and b are added. The displayed cancellation checks d²=0 before each extension. The identity of Z is closed, so the h-extension is also legitimate.

For step 2, I read `lem-coef-dgcat-formal-cone-enlargement`: its statement contains D_u, the differential of module maps, the coordinate degrees and the biproduct equations. Substituting the four coordinate maps gives exactly the four displayed equations. Step 3 uses the actual signed Leibniz rule from the free-cell statement, not a sign-free composition rule. I recomputed all four lines: the degree-one projection contributes a minus sign, and the two defined negative components produce db_h and dw_h as stated. All outputs have old-object endpoints and the expected degrees. These are short substitutions, marked elementary, rather than new lemmas.

Step 4 uses free adjoining and the Leibniz word differential, which the free-cell statement actually gives. It evaluates the free words and checks d on the generators, hence on every word; there is no appeal to an unstated presentation theorem or to a proof hidden inside a dependency. Step 5 uses the explicitly stated entrywise cone extension from the formal-cone node. I checked that its images of coordinate maps are the corresponding coordinate maps because their matrices contain only zeroes and identities.

For step 6 I used the formal-cone statement's degree matrix and differential D_v M - (-1)^n M D_u with n=-1. I recomputed the four entries of dH: -db+uv, -dw+ua-bu, -dv, vu-da. Each gives the relevant identity or zero by the equations already constructed in step 1. The two diagonal identity entries are on the two graded summands, even when x=y. Step 7 uses free adjoining again, now with the checked equality dH=J(1_Z). The explicit word evaluation explains why the extended assignment is a dg functor.

Step 8 uses the formal-cone statement's full isomorphism of Hom complexes between representables, including its composition and unit compatibility. The restriction has representable object images, so taking these inverse Hom isomorphisms defines G on every morphism and preserves d and composition. It is not an assertion that arbitrary cone objects were already in B. The coefficient formula is literally j on each matrix entry. Step 9 uses the same statement's coordinate projections and ordinary matrix composition; the four corner selections recover v,a,b,w with the required signs. These verifications supply each clause, including the more precise extension and factorization.

For B1–B10, there is no unsplit new node, no uncited new notion, no new Mathlib-leaf claim, and no attachment to a partial or sorried declaration. The copied item statement, source, inherited searches and audit metadata were retained. Every newly recorded search really ran and its hits were read. For C1–C8, every non-elementary construction is one of the two cited statements; all nine steps have exact statement quotations in citations.json; their proof dependencies are exactly the union of the uses lists. Both construction nodes have the item's unit, so there is no off-unit tool declaration. No parent is cited, eliminating a possible cycle. For D1–D5, the proof carries the sign calculation and the actual functor constructions rather than renaming clauses as new lemmas. For E1–E7, the hypotheses used are precisely the stated smallness, R-linearity, cochain convention and du=0. No item statement dispute was found; the source-display sign issue is recorded below.

I tested the equations when u=0 (both endpoint identities become boundaries in the free extension), when x=y and u=1 (the two cone summands still have separate coordinates), in characteristic 2 (all sign identities remain valid), and over the zero ring. None requires distinct endpoints or a nonzero ring. An empty category has no chosen arrow, so cannot instantiate the hypotheses; no nonempty conclusion is inferred from that case. All nine steps have fewer than 2000 characters; each elementary portion is the stated finite calculation. No hidden long comparison or standard lemma needs a further node.

The resumed sandbox initially contained only dispatcher brief markers and there was no active delivery for this item. I therefore did not repeat an interrupted mutation. This review is the author's signed self-check for direct delivery; the maintainer performs the independent review.

## Source error

On continuation I reread the primary PDF's Proposition 1.7, printed p. 27, together with the preceding presentation of K. Its extracted display writes the contraction as [[r_2,r_12],[g,r_1]], while the preceding equations say dr_2=fg-1 and dr_12=fr_1-r_2f. With the differential and cone convention printed there, the upper-left entry of dH for that displayed positive matrix is dr_2+fg=2fg-1, not 1. For a concrete check over Z, take x=y to be the contractible two-term complex Z -> Z with identity differential, let k be its degree-minus-one contraction, and set f=g=r_12=0 and r_1=r_2=-k. All the printed generator equations hold, but the displayed positive matrix has differential diag(-1,1). The matrix [[-r_2,-r_12],[g,r_1]] gives the required identity instead. This is a sign error in the source display, not a defect of the dispatched statement: the item already has exactly these two negative signs, and steps 3 and 6 verify them directly. No statement, dependency, or proof has been changed. The earlier report's blanket assertion that there was no source error is corrected by this paragraph.

The interrupted dry-run log contained only its preparation line. I checked that no deliver.py or srvcheck.py process for this item remained active before starting the resumed dry run, and have kept that single resumed invocation active while it waits. I compared the sandbox node with the current repository, retained its nine proof steps and inherited evidence, reread both current dependency statements, and checked every citation quote against them. No new search was needed because neither the statement nor the search question changed.

## Dry-run repair

The first resumed dry run exited with one B4 diagnostic on step 6: the checker interpreted the legitimate matrix row break immediately followed by the entry v as a doubled TeX command. I separated the row break and that entry by a space, standard TeX whitespace, without changing the formula or its meaning. No other check failure was reported. This diagnostic is also reported here because the checker conflates an unspaced matrix row with an escaped command; no project or launcher script was edited.
