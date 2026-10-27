# Stage-1 delivery: lem-sfb-nodal-point-blowup-local-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-point-blowup-local-descent.json: existing statement, now split in eight steps. No Mathlib match for the entire statement.
- citations.json: 25 verbatim full-statement quotes, one for each step/node citation.
- searches.jsonl: five fresh searches made through the required msearch.py command and read before recording verdicts.
- report.md: this report. No new nodes and no new Mathlib leaves.

The initial sandbox contained only dispatcher brief markers, so there was no previous proof or search log to reuse. I copied the current item and preserved its statement, statement dependencies, source, created record and blueprint history. Temporary write_split.py stays in the item sandbox; no Lean, repository, launcher, compiler, Lake or git command was used or modified by the worker.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and the word nodal found only comments/docstrings about unrelated counterexamples; no declaration proves this point-blowup statement. The project has general blowup infrastructure, which does not provide the entire nodal descent theorem. The existing model-calculus node is broader but does not give all conclusions of the item about an arbitrary X, the reduced-centre shrinking and coverage. It is used as a genuine tool rather than an attachment.

## WANTED

None. The primary sources needed for this split are present locally in literature/stacks-project/.

## Errors and corrections

The item itself is mathematically correct and was not weakened or changed. Its imported proof was empty. I filled it by the source's two Cartesian blowup comparisons and its residue-field argument, including details that are essential when the node is not split over the original residue field.

### Source error

Stacks models.tex Tag 0CDE, final paragraph, says that for n>2 the model blowup has a unique singular point. This is false for n=3: its middle chart is R'[r,s]/(rs-pi), which is regular, as the earlier n=1 calculation in Tag 0CDC already proves. The two outer charts are regular too. Thus n=2 and n=3 are both stopping cases. A residual nonregular point exists exactly for n>=4, with exponent n-2. The item had already corrected this source error; this delivery retains that correction and spells it out in steps 4 and 7. The sentence in 0CDC saying 'except for one point' likewise means 'except possibly' for the stopping cases. No STATEMENT-DISPUTED correction to the imported item is needed.

The blueprint ancestry tool returns blueprint.from.node = None for this inherited non-blueprint chain, as in the current item. I preserved it, the detailed place and via list, and searched all blueprint nodes for nodal and the relevant blowup/locality tags. No equal blueprint statement was found. Chapter and unit records were read; no unit route or realization was edited. This item supplies a subordinate regularization input to the direct-image alteration route, not the unit's key theorem.

## Unfinished work

None within this one-level stage-1 split. The existing cited unsplit nodes retain their own proofs as future items. No new statement-only obligations were required.

## Not duplicates

No new nodes. Whole-DAG keyword/tag searches for 0CDE, 0CDC, 0805, nodal blowup, etale stalk regularity, nodal locality and reduced-centre comparisons located the existing tools. In particular I reused lem-sfb-dvr-nodal-chart-blowup-calculus, lem-sfb-flat-pullback-blowup-chart-restrictions (read for the stronger chartwise centre comparison, though the proof uses the generic flat-blowup theorem), lem-trf-nodal-family-etale-source-locality and lem-sfb-space-nodal-chart-locality rather than creating statements restating these or the item's clauses.

## Review by Q129

I read the chapter record sec-six-functors-basics and the full sk-thm-sf-ctf-stability unit record, the item's parent regularization node, and Stacks models.tex Tag 0CDC (example-blowup) and Tag 0CDE (lemma-blowup-at-worst-nodal), including the complete comparison and termination paragraphs. I also read divisors.tex Tag 0805, curves.tex Tags 0CD8 and 0C5D, spaces-more-morphisms.tex Tags 0DSF and 0DSG, more-algebra.tex Tags 07QP and 0AH0, morphisms.tex Tags 01TE and 01TF, and etale.tex Tag 025O. The supporting algebraic and completion calculations are exactly the existing nodes' statements, which I read in full. There are no new nodes needing their own source audit.

Step 1 uses lem-weil-pbc-etale-fibre-discrete-separable-points for the full reduced scheme structure and finite separable residue extensions, not just discreteness. Its statement explicitly describes the singleton component as Spec kappa(u). Since a singleton is open in each fibre's subspace topology, two open neighbourhood restrictions isolate it in both fibres simultaneously. The closed points x and o make these singletons closed in the restricted U. The open restriction and composition facts are exactly the clauses of lem-weil-pbc-etale-composition-cancellation. No residue fields are identified.

Step 2 cites def-weil-etale-morphism only for its actual flatness clause. The construction def-nagata-blowup-flat-base-change-map introduces the correct comparison and orientation, and thm-nagata-blowup-flat-base-change asserts that this comparison is an isomorphism. I checked the source theorem has no properness or excellence hypotheses. Both centres are genuine inverse-image closed subschemes by step 1. The etale base-change node states stability for every scheme base morphism, hence applies to the two blowup maps. The surjective-base-change node says exactly that any base change of a surjective scheme map is surjective. Applying it to the single-point spectrum of the field extension proves coverage of all exceptional points, not only a neighbourhood of one chosen lift.

Step 3 uses thm-nagata-global-blowup-complement on the ideal of the reduced point. It explicitly asserts the desired isomorphism off the support. The generic fibre avoids this special-fibre support. Open immersions are etale by the cited permanence node. No separate assertion of blowup surjectivity or connected exceptional fibres is used.

Step 4 reads the statement of lem-sfb-dvr-nodal-chart-blowup-calculus, which gives all three actual chart equations, their morphisms, flatness and the exact regularity cutoff. It applies over R' because R' is a DVR and pi is its uniformizer. To avoid taking purity or the precise completed-ring convention from an ambiguous use of 'nodal', I also cite lem-sfb-binomial-geometric-fibres (reducedness, pure dimension one, smoothness off the crossing) and lem-sfb-monomial-local-completion at the monomial ideal generated by the exponent (1,1). The last is a genuine monomial quotient-completion theorem, not merely exactness of completion. The residue field at the middle origin is visibly R'/(pi); this last calculation is elementary. In n=2 the middle ring is Laurent, in n=3 exponent one, and in n=4 the residual model is the first nonregular model, exponent two. These cases also work in characteristic two and for imperfect original residue fields.

Step 5 uses the existential source-and-target-chart criterion of lem-sfb-space-nodal-chart-locality in its scheme specialization, with the identity on B and Spec R' -> S. The identity supplies the explicitly required surjectivity. This directly covers composition with an etale base map; I do not silently use a target-base-change result to claim postcomposition. Then lem-trf-nodal-family-etale-source-locality applies first to {id_B,q+}, which is a covering even if q+ is not surjective, and then to the two-member cover of X+. Its statement explicitly provides flatness, local finite presentation, purity and the required completed local rings without global Noetherianity, connectedness or nonemptiness hypotheses. The comparison is source locality, not a stronger finite-presentation theorem.

Step 6 handles reducedness separately because that word is not explicit in the cited source-locality statement. The etale-fibre node applies to Spec R' -> S over the chosen geometric point, making its fibre a disjoint union of copies of Spec Omega, since every finite separable extension of an algebraically closed field is trivial. The binomial-fibre node gives the reduced charts of B_Omega. The etale-base-change node and etale-proposition-etale-reduced give reducedness on U+_Omega. The surjective-base-change node preserves the coverage already established at the exceptional fibre; the complementary open covers all other points. Finally lem-sfb-etale-stalk-invariants states faithful flatness for the indicated local homomorphisms. I wrote the two-line module argument for injectivity from faithful flatness, so reducedness reflects to the local rings downstairs. This uses neither a nonexistent reducedness clause in the regularity node nor a completion/excellence assumption.

Step 7 cites lem-sfb-etale-stalk-invariants for the actual equivalence of regular local rings under etale maps. Surjectivity above x was proved in step 2. The fibre of w+ over o is Spec kappa(o), so its pullback to Spec L is exactly Spec L, not a product of unknown length. This is the reason one nonregular point upstairs implies precisely one downstairs. For n=2,3 all lifts are regular; for n>=4 the single lift is nonregular and every other point is regular. An arbitrary etale cover without the Cartesian fibre calculation would not justify uniqueness, and I checked that no such inference is made here.

Step 8 restricts to the inverse image of the explicit middle affine open, and cites the etale open-restriction/composition clauses for both maps. It proves closedness from finite residue fields: the locally finite presentation definition gives a finite-type affine chart of the special fibre around x; lem-kun-closed-point-field applies only to that affine chart, not to a possibly non-quasi-compact fibre. The finite separable extensions from step 1 and the displayed fibre formula give kappa(u+)=L finite over k, so its subfield kappa(x+) is finite over k. The locally-finite-type hypothesis of lem-trf-finite-residue-point-closed-in-fibre follows directly from the local finite-presentation presentations established in step 5. The theorem makes x+ closed in the special fibre; because that fibre is closed, it is closed globally. Thus no properness, projectivity, separatedness or excellence hypothesis is being smuggled into this argument.

Against delivery-errors B--E, I checked the statement is self-contained, definitions and source tags are retained, no proof is hidden in a new statement, no item clause is relabelled as a new lemma, and every non-elementary assertion above is covered by a cited statement. All eight proof steps are shorter than 2000 characters and each carries its source; none is marked elementary merely to evade a missing citation. citations.json contains an exact quote for every used node. All cross-unit generic tools are explained in split_report.tool_uses: they preserve the prescribed blowup route and supply generic locality, residue-field or blowup comparisons. No changed statement, duplicate node or dependency on the parent regularization node creates a circular proof.

The five fresh Mathlib searches were actually run through msearch.py, and their results were read. LeanFinder returns standard-etale coordinate constructions and generic morphism base-change stability. LeanSearch returns Weierstrass nonsingular-point and good-reduction facts. Loogle reports the project-only blowup identifier unknown in Mathlib. The source grep finds no blowup implementation under Mathlib/AlgebraicGeometry. These are not exact matches or one-line specializations of the item. The original item's historical search entries were retained and the actual new results appended; no query was invented.
