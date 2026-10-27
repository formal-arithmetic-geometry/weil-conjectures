# Q81 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-chart-rational-point-taylor-iso.json`: statement, split into seven proof steps; unchanged statement; no exact Mathlib match.
- `citations.json`: a verbatim statement quote for every use in every numbered step.
- No new nodes or Mathlib leaves. The sandbox also retains the search log and preparation script.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint id, Taylor coordinates, and etale/completion notions found no project declaration giving the full statement. In particular a theorem about strict henselization completion flatness or a Taylor polynomial calculation does not identify the completed local ring of an arbitrary etale chart with the specified coordinate power-series ring.

## WANTED

None.

## Audit findings and changes

The imported statement is correct, including arbitrary field extensions, the structural rather than abstract identification of the residue field with L, uniqueness among homomorphisms satisfying all finite-level formulas, and the extra assertion about the uncompleted local ring when n=0. No statement correction or dispute was needed.

The item was introduced to fill a real gap in the parent Taylor-comparison proof: the algebraically closed coefficient-field hypothesis of `lem-trf-etale-completed-local-ring-iso` is unavailable here. I did not use that special-case theorem. The proof instead invokes the existing general flat-local-completion isomorphism after checking its exact hypotheses. The polynomial completion ingredient already has a sufficiently general existing node, `lem-trf-monoid-completion-coefficients`, so no new local-coordinate or polynomial-completion lemma was created.

The item's blueprint ancestor is `lem-trf-local-term-locality`, through the retained historical modification branch and the Taylor normal-cone comparison. I read the chapter and unit records and retained their route; this is only the lower local-algebra input the ancestor chain already names. Searches of the whole imported blueprint for completion, power series, etale chart, and 039M found no equivalent blueprint node; `same_as` remains empty. The blueprint text and parent fields were preserved.

The logged first semantic Mathlib search returned standard-etale definitions and existence of etale polynomial coordinates, not completed local rings. The second phrasing, about flat local homomorphisms with equal residue fields and maximal ideals, returned completion flatness, completion of an already complete algebra, and completion functoriality; none asserts the needed isomorphism of completions. Loogle `AdicCompletion, Algebra.Etale` returned zero hits. The grep found `MvPowerSeries.toAdicCompletionAlgEquiv` at `Mathlib/RingTheory/MvPowerSeries/Equiv.lean:344`; I read it and its adjacent component/truncation formulas. It identifies a polynomial completion, so it is an ingredient rather than an attachment or a one-line specialization of this scheme theorem. The existing monoid coefficient theorem already gives that ingredient. LeanSearch was rate limited; its actual failure is recorded as unavailable, not as evidence of absence. I also read the base-change instance in `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:74` used by the existing Mathlib leaf. Searches from the original node were retained as historical data, and the five new entries reproduce the actual logged queries and outcomes.

## Not duplicates

No new nodes. I searched the whole DAG by the source tag 039M and by the etale-completion and polynomial-completion concepts before deciding to reuse the existing general results. In particular no duplicate of the algebraically closed etale-completion node, the flat-local-completion theorem, the smooth-rational-point theorem, or the monoid coefficient theorem is introduced.

## Review by Q81

I read `literature/stacks-project/etale.tex`, `lemma-characterize-etale-completions` (039M) and the following residue-degree remark, together with `more-algebra.tex`, `lemma-flat-unramified` (0AGX), including its proof. The former gives the advertised etale completion route and the latter states exactly the general flat local completion isomorphism used here. I read `morphisms.tex`, `lemma-base-change-etale` (02GO), `lemma-unramified-at-point` (02GF), and `lemma-finite-type-noetherian` (01T6), and `algebra.tex`, `lemma-Noetherian-permanence` (00FN) and `lemma-hathat-finitely-generated` (05GG). There are no new nodes whose independent source requires checking. I read the statement of every cited existing node, and also the coefficient construction in the proof of the monoid completion node. The latter is an existing general tool within this unit, not a new use of any SGA route.

Step 1 cites etale scheme base change, which says exactly that the second projection after arbitrary base change is etale. The affine-space node explicitly gives the polynomial spectrum over an affine base; the polynomial node gives evaluation and its uniqueness. Translating variables therefore identifies the actual image point with the evaluation prime. The affine-stalk theorem, clause (c), states the localization and the germ formula required to identify A and its coordinate map. Evaluating the coordinates proves that the structural residue maps are identities under the specified L-identifications; no assertion about an algebraically closed field enters.

Step 2 cites the finite-type Noetherian and localization Noetherian nodes exactly for those two permanence operations. The locally Noetherian definition supplies a Noetherian affine cover, and the locally-finite-type permanence theorem applies to the etale morphism because the unramified definition supplies local finite type. I checked that it is local finite type, rather than global finite type, throughout. The affine-stalk clause (c) and localization permanence then give Noetherianity of B. The field is nonzero and Noetherian for the explicit elementary ideal reason; no additional hypothesis on U is needed.

Step 3 obtains flatness of the actual local stalk map from the etale and flat-morphism definitions. The unramified maximal-ideal criterion says precisely that an unramified open neighbourhood of b gives m_A B=m_B and a finite separable residue extension. The whole source is such a neighbourhood, and its local-finite-type hypothesis was checked in step 2. I use the residue identity from step 1 rather than mistakenly inferring triviality from separability alone. The flat-local-completion node explicitly states the actual componentwise completed map, not just an abstract ring isomorphism; all of its Noetherian, locality, flatness, maximal-ideal and residue-field hypotheses have now been verified. Its component formula is exactly what later proves the Taylor formula. The off-unit theorem is declared as a general local-algebra tool in split_report; it preserves the unit route.

Step 4 applies the monoid coefficient statement with A=L, m=0 and P=N^n. I checked finite generation, the embedding in Z^n, the total-degree positive weight, and zero-adic completeness and separatedness of the field. The elementary standard-basis decomposition proves nu(E)=|E|. The node explicitly states both the natural coefficient isomorphism and the coefficient criterion for each projection kernel, which prove the finite truncation formula; the multivariate power-series definition states exactly the same coefficientwise addition and convolution. This step does not merely assume a formal series evaluation map into an uncompleted ring. It reuses a strictly more general existing node instead of introducing a node restating the item.

Step 5 is the elementary localization comparison, proved rather than cited by a bare tag. For every denominator outside J, its constant term is a unit and its remainder is nilpotent modulo J^r. The finite geometric sum written in the step is its inverse. The fraction definition of localization therefore gives inverse quotient maps. Their agreement with reduction follows on the polynomial generators and on denominators, giving inverse maps on compatible sequences by the completion definition. This calculation requires neither a completion-localization commuting theorem nor an assumption that localization commutes with arbitrary inverse limits.

Step 6 composes the three actual maps, using the explicit finite-level formulas established in steps 3--5. The value at every level is the required finite Taylor polynomial. Equality of compatible sequences proves uniqueness among homomorphisms satisfying the formula, so no hidden automatic-continuity theorem is used.

Step 7 cites the completion-local-ring theorem, whose statement gives exactly the maximal ideal m_B completed and the structural residue identification. The localization definition gives m_A=JA, and step 3 gives m_B generated by the coordinate differences. An isomorphism sends the variable-generated ideal to the ideal generated by their images; the r=1 formula gives the residue identity. For n=0, m_A=0 forces m_B=0, and the given structural residue isomorphism proves B=L even before completion. This last conclusion was checked rather than dropped.

For small cases I checked the identity chart on affine space at an arbitrary rational point c, including nonzero c; translation produces the correct coordinate differences. I checked n=0 (including an etale scheme with several points: only the chosen stalk is L), and n=1 over a non-algebraically-closed field with any field extension L. A nonrational point is excluded by the hypothesis and must not be substituted into the residue identity argument. Characteristic does not enter any calculation. The empty-variable free monoid satisfies the positivity hypothesis vacuously and its coefficient ring is L, so the same step 4 remains valid.

Against delivery-errors B--E: no new unsplit nodes, hollow restatements or duplicates were added; the unchanged statement is self-contained with its original definitions; each non-elementary inference is supplied by a cited node whose statement I read; no proof of a node is used for an unstated strengthening. The explicit translation, denominator inversion, component composition, and zero-variable arguments stay in the proof as elementary steps or calculations inside the corresponding applications. All steps are below 2000 characters. No clause was moved wholesale to a new node, no new cycles were intentionally introduced, and the route and statement were preserved. The server review_split check has passed with zero new nodes; the full delivery dry run is the next gate.

## Unfinished work

None within the stage-1 split. Existing unsplit or sorried dependencies remain independent DAG work, as required; no Lean was written or compiled.
