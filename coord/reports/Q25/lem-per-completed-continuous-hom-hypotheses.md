## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-continuous-hom-hypotheses.json`: existing statement, now split in five steps; no Mathlib match.
- `citations.json`: verbatim extracts for every step/node citation.
- `searches.jsonl`: five new searches executed through msearch.py; all services answered.

No new DAG nodes and no Mathlib leaves. The statement, statement dependencies, source, chapter, unit, creation stamp, and blueprint ancestry are unchanged. No repository files or Lean files were written, and no compiler was run.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` for the exact blueprint tag, completed/continuous coefficient terminology, constructible Hom sums, and scalar restriction equivalences. No declaration proves every clause of the item. Ordinary module coefficient equivalences and continuous group-cohomology comparisons concern different categories.

## WANTED

None.

## Problems found and changes

The item was a statement-only obligation extracted by Q133 from retained steps 1-2 of the rational Hom comparison. No repair note exists for this item, and there was no previous sandbox node, report, search log, or active delivery when this continuation resumed. The statement does not need a correction. The substantial source assertions already have nodes: creating further copies of the Hom-sums or stratified characterization would be a duplicate. The normalized transport node also already supplies the general exact derived coefficient equivalence.

I retained the full statement and supplied its argument. In particular, I did not infer ordinary boundedness just from a uniformly bounded reduction tower: I used the witness-sensitive equivalence (i) iff (iii) of the existing characterization. I did not infer a specific shifted-coprojection square merely from a bare equivalence: step 5 writes its equation on every summand. The coproduct preservation argument in step 2 is the universal property with the inverse equivalence, rather than an additional lemma.

Mathlib queries were read as returned. Loogle supplies `SheafOfModules.restrictScalars` and its additive instance, not the derived constructible assertion. The source in `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` defines that ordinary functor at lines 34-43. Grep also finds `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` at `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:296`; I read lines 291-307, which concern ordinary modules over rings. The second semantic phrasing finds exact derived-functor linearity and sheaf pushforward comparisons, not constructible adic Hom continuity. Condensed AB5 and finite algebraic adic completion hits from the first semantic search are also different assertions. Existing historical item searches have been retained; five searches actually run for this delivery were appended from the new log, with the exact tool/query pairs.

## Not duplicates

No new nodes. Whole-DAG searches for the cited Bhatt–Scholze places, ring-isomorphism transport, coefficient equivalences, and Hom sums found the three substantive tools actually used. Blueprint search for `coproduct`, `continuous`, `restriction of scalars`, `Hom sums`, and `coefficient transport` found no equivalent blueprint statement for the whole item. The nearest blueprint ancestor is `lem-per-smooth-pullback-t-exact`, as confirmed by blueprint_refs.py; its current main-20261015 text and the fixed chapter/unit records were read. This item supplies the continuous-realization obligation beneath its first cohomology/pullback argument; it is not a key node of the unit, so no unit realization fields are changed.

## Review by Q25

I read Bhatt–Scholze, printed pages 58-62, directly from the local PDF. Lemma 6.8.2(1) identifies completed and continuous integral coefficients using quotient projections. Proposition 6.8.11(3) says constructible integral complexes are bounded with constructible cohomology. Lemma 6.8.12 gives RHom preservation of direct sums in a common lower half-plane (the printed statement uses D^{>=0}); the existing Hom-sums node spells out arbitrary common lower bounds and shifted coprojections. I also read Stacks Tag 015F, `derived-lemma-right-derived-exact-functor` in derived.tex: the unbounded derived functor of an exact functor is computed on every complex. Tag 03D7, `sites-modules-lemma-adjoint-pullback-pushforward-modules`, was read as background for the existing general ring-isomorphism transport statement, not cited as a replacement for it. No SGA source is used. There are no new-node sources to review.

For step 1 I opened `lem-per-rational-module-realization-functor` and `lem-pur-ring-iso-derived-transport`. The first explicitly gives the quotient-projection coefficient identification, preservation of constant sections, and locally closed restriction. The second explicitly gives `(alpha^{-1})_*`, its inverse, termwise derived normalization, and roof comparison. Thus the orientation B_X-modules to A_X-modules is correct. Constant A-scalars have the same action, so the same numerator maps on roofs give A-linearity; no projectivity claim is used. The site is taken in a universe where its representative is small, as the transport theorem requires.

For step 2 I checked the cohomology definition and the transport theorem's termwise normalization. Kernels and images are unchanged as abelian sheaves, and the scalar action changes exactly as in the ordinary functor; the same statement applies to quasi-isomorphic representatives. Integer shifts change degrees and differential signs only, so the identity on transported terms defines the natural shift comparison. I wrote the three Hom bijections showing that the transported coprojections satisfy the coproduct universal property, including the empty case. This is an elementary consequence of the already cited equivalence, not an uncited assertion that this particular functor preserves colimits.

For step 3 I opened `lem-weil-pbc-integral-stratified-perfect-characterization`, including its entire statement rather than just the title. Its condition (i) includes the compatible etale-origin witnesses, its condition (iii) supplies actual boundedness, and its final sentence supplies every integer shift. The transport theorem gives the tensor comparison, and the realization theorem gives locally closed coefficient compatibility, so the local finitely presented models are unchanged under e. Applying the characterization in the identified coefficient presentation retains the witness condition. I checked that the hypotheses are exactly finite E/Q_l, noetherian finite-dimensional X, and invertible l, all present here. No flatness or projectivity of the finitely presented modules is assumed. No completeness of an infinite coproduct is asserted or needed: the M_i belong to the ambient derived category.

For step 4 I read the complete statement of `lem-weil-pbc-integral-constructible-hom-sums`. It applies to the continuous coefficient category using its canonical completed identification, to a completed bounded constructible source object, and to every small countable target family with a common lower bound and every q. These are supplied by steps 1-3 with the identical X, A, and e. Its conclusion explicitly names the shifted-coprojection map and allows the empty family. Thus it supplies exactly the second map in this item, not only a noncanonical isomorphism between its endpoints.

For step 5 I checked the equation on a representative u in each summand: shift naturality moves T(iota_i[q]) through s, and the equation c T(iota_i)=j_i gives the desired component. The direct sum universal property then proves equality of the actual maps. Both vertical maps are A-linear bijections from the equivalence already proved. The empty family has zero objects and zero Hom groups. This completes the first map by conjugation, with no additional lemma or hypothesis.

Edge cases checked: X empty, K=0, the empty family, a singleton family, torsion integral cohomology such as A/varpi on a geometric point, and positive or negative q. In the torsion example the relevant module is not flat over A, which confirms why no such assumption was introduced. Arbitrarily descending lower bounds on a countable family are deliberately outside the statement; nothing in the proof claims compactness for that family. All five steps are under 2000 characters (the longest is 1081); no long step hides a separate comparison theorem. I also traced the statement/proof dependency closures of the three tools and the realization node to check that none reaches this item, so these citations introduce no cycle.

I checked delivery-errors B-E point by point: there are no new self-containedness, source-tag, search-log, or duplicate obligations; all step citations have verbatim statement extracts; the two elementary steps explicitly give their calculations; no cited proof is used as an unstated interface; the item is not moved into a new node; the scheme and coefficient hypotheses agree throughout. Three off-unit citations are declared as generic tool uses in split_report: normalized ring-sheaf transport, the completed integral characterization, and bounded-below Hom continuity. They do not change the perverse unit route. No mathematical correction was necessary.

## Unfinished work

None in this one-level split. The required server dry run and delivery are the remaining verification steps.
