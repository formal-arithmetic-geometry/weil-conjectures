## Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-complete-coefficient-datum.json: definition, split; no exact Mathlib match after two semantic phrasings, Loogle and source grep.
- citations.json: verbatim cited statements for every step.
- No new nodes and no Mathlib leaves.

## Attachments

None. The blueprint tag has no declaration in WeilConjectures/. Read DerivedCategory/Complete/Defs.lean: Ideal.quotPowFunctor (line 169) supplies quotient transitions and DerivedCategory.derivedCompletionDiagram (line 372) supplies the ambient reduction diagram. Neither supplies the normalization over the quotient coefficient ring, so these are only partial coverage, not an ATTACH. ProEtale/Derived/Tensor.lean supplies a general derived tensor, not the whole item.

## WANTED

None. The source documents used are present locally.

## Corrections and scope

The imported definition had no statement dependencies and left X, commutativity, coefficient sheaves, index range, and coefficient categories implicit. Named existing definitions, introduced X as a scheme, made positive indices explicit, defined additive torsion inline, and specified the target D(X_proet,P_n) of reduction. Retained the Noetherian, finite-generation, torsion and perfectness hypotheses, although the construction and normalization hold without them. No completeness assumption was added: the title is not a hypothesis. The named normalization is derived extension of scalars, not tensoring twice over Lambda.

The transition and normalization clauses are verified in four construction steps within the item; no new node simply restates a clause. The formulas select actual data and prove the identities, rather than selecting unspecified data from an existence theorem. These steps are supplied even though the item is a definition, so its embedded identities are reviewable.

Do not substitute def-weil-pbc-adic-coefficient-datum: its coefficient sheaf is the inverse limit of locally continuous finite quotient sheaves, and it assumes finite quotient sets. This item uses the constant Lambda sheaf, arbitrary perfect quotient modules, and no completeness or finite-set requirement. Also do not use lem-weil-pbc-proetale-derived-pullback-composition: its ring identifications exclude the coefficient change Lambda to P_n. lem-pc-derived-tensor-transitivity concerns one-point ring modules and does not itself give quotient-ring-valued sheaf extension. The original target declarations in upstream master Proper.lean lines 74–118 concern condensed E and padicAlgCl coefficients, finite-type separated schemes over a field of positive characteristic different from ell, and the specified cartesian exchange morphism; both are sorry. This split establishes no comparison with those condensed coefficient categories and does not claim to prove those targets.

## Not duplicates

No new nodes. Blueprint searches for reduction tower, complete-coefficient, K-flat and extension of scalars, and whole-DAG searches by statement, ring change and source tags led to the existing generic sheaf-ring results. Nearby tower definitions are different coefficient data, as explained above.

## Unfinished work

None for this one-level definition split. Dependencies retain their repository states. No compilation, Lean editing, live-project editing or delivery push was performed by this worker.

## Review by NH

I read the item's complete master blueprint source, its chapter and unit records, and the inherited stage-1 rules including delivery-errors B–E. The unit's three steps prove torsion proper base change; this auxiliary coefficient construction replaces none of them. I also read the actual statements of all cited nodes. For the analytic normalization argument I read sites-cohomology.tex, the K-flat pullback lemma 0G7E, the derived pullback construction 06YY, and the composition proof 0D6D, and sites-modules.tex Section 03EK, including the sectionwise tensor and sheafification definitions. These apply to identity topoi with arbitrary coefficient-ring maps; they do not require flat quotient rings. No new source node is needed.

Step 1 uses lem-pc-kflat-resolution exactly for a resolution with K-flat source and flat terms, def-weil-pbc-proetale-site for the constant sheaf ring and its module-derived category, and lem-pur-derived-change-of-rings for computation in D(P_n), with its resolution comparison. I checked that the latter's statement is for an arbitrary site and arbitrary sheaf-ring map, so the quotient map is within its hypotheses.

Step 2 uses def-weil-pbc-algebra-hom-quotient for powers and quotient algebra structures, def-pur-sheaf-tensor-product for the actual sheafified change-of-rings construction, def-pc-sheaf-restrict-scalars for its unchanged underlying abelian sheaf, and lem-weil-derived-tensor-functorial for identities and composition. Exactness of restriction here is written out through unchanged kernels, images and cohomology, rather than borrowed from the narrower completed-DVR restriction lemma. The quotient class calculation proves the transition identities before localization; this is elementary.

Step 3 uses lem-pur-kflat-change-of-rings exactly for K-flatness with flat terms over P_b, then lem-pur-derived-change-of-rings for computing extension to P_a on that model. The sheaf tensor definition gives the sheafification of sectionwise balanced tensors. The explicitly written forward and inverse formulas respect both balancing relations and restrictions and commute with the differential. Thus no uncited derived associativity theorem is hidden in the argument, and no finite-Tor or flatness hypothesis on the quotient was assumed.

Step 4 uses the sheaf tensor construction and the same K-flat preservation statement. Both paths are computed on a single model and take the displayed triple tensor to the identical expression. Equality is checked locally on tensor generators, so it survives sheafification and derived localization. It proves the cocycle itself, rather than citing a definition as if it proved coherence. The same formula at equal indices gives the unit law.

I tested I=Lambda (zero quotient), K=0, equal indices, an empty scheme, I=0 over a torsion Noetherian ring, and Lambda=Z with I=(p). All formulas remain defined and satisfy the identities. In the last case P_b is generally not flat over Z; its extension model is nevertheless K-flat over P_b, which is precisely the distinction used in step 3. The retained perfectness assumption is about P_n over Lambda and is not misread as flatness. All citations are copied verbatim into citations.json. General sheaf lemmas from other units are declared as tool uses with their exact purpose.

The Mathlib searches ran through msearch.py and are recorded with their literal queries. LeanSearch returned HTTP 500 and is recorded unavailable. The two LeanFinder phrasings gave local-cohomology/Tor/Ext and underived pushforward results respectively. I read Mathlib CategoryTheory/Monoidal/Tor.lean lines 35–67 and Sheaf/PushforwardContinuous.lean's declarations: neither supplies an unbounded quotient-coefficient normalization tower. The first Loogle query rejected the identifier tensor, explicitly recorded as no evidence of absence; subsequent quoted-name searches ran normally. The source grep found no derived scalar-extension/K-flat implementation. No search that was not run is recorded.

## Earlier second reading (a previous round; superseded)

- Item statement: compared every hypothesis and clause with the complete master blueprint definition, order 1255, and its unit/chapter sources; PASS. Noetherianity, finite generation, additive torsion, perfectness, quotient transitions and the quotient-ring normalization all agree. Constant coefficients and positive indices are explicit; completeness is not assumed.
- Step 1: read the statements of lem-pc-kflat-resolution, def-weil-pbc-proetale-site and lem-pur-derived-change-of-rings against sites-cohomology.tex labels lemma-K-flat-resolution (06YS) and lemma-derived-base-change (06YY); PASS. An arbitrary unbounded complex on this ringed site has the required model and canonical derived comparisons.
- Step 2: read def-weil-pbc-algebra-hom-quotient, def-pur-sheaf-tensor-product and def-pc-sheaf-restrict-scalars against the quotient definitions and sites-modules.tex section-tensor-product (03EK); PASS after repair. Ideal containment and quotient composition are elementary; restriction preserves cohomology, and the displayed chain-map calculation now checks compatibility of transitions with resolution comparisons.
- Step 3: read lem-pur-kflat-change-of-rings and lem-pur-derived-change-of-rings against sites-cohomology.tex lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY) and lemma-derived-pullback-composition (0D6D), and read def-pur-sheaf-tensor-product against 03EK; PASS after repair. All are applied to identity topoi with the indicated sheaf-ring maps. The inverse formulas satisfy both balancing relations and commute with differentials; the added formula verifies naturality under model comparison, rather than just asserting independence.
- Step 4: read def-pur-sheaf-tensor-product and lem-pur-kflat-change-of-rings against 03EK and 0G7E, and compared the explicit computation with 0D6D; PASS. The two paths have exactly the same triple-tensor value; this is an elementary calculation on the models established in step 3. For sheafified tensors these generators are local generators, sufficient for equality of sheaf maps.
- New nodes: none; B1–B7 and duplicate/Mathlib-leaf conversion checks have no new nodes to examine. Read the existing cited statements directly, and verified that citations.json remains verbatim after removing the unnecessary citation.

Small cases checked independently: K=0, the zero ring and I=Lambda, an empty scheme, I=0 over a finite field, and equal indices including n=1. All formulas satisfy the asserted identities. The definition uses n>=1; if extended to n=0, I^0=Lambda gives P_0=0 and the same formulas still hold. For Lambda=Z and I=(p), nonflat quotients do not invalidate step 3: K-flatness is required over P_b after extension, and 0G7E supplies exactly that property.

Independent source search: msearch.py grep query `extensionOfScalars|scalarExtension|tensor.*[Aa]ssoc` returned 25 hits in complex/graded-object/Dialectica/site monoidal calculations; these do not state a derived quotient-ring-valued normalization tower. There are no new nodes requiring further Mathlib leaf searches. Read the actual slopmaster2 CategoryTheory/DerivedCategory/Complete/Defs.lean lines 169–173 and 372–376: quotient and ambient derived diagrams are partial coverage only, not this coefficient-change normalization. No sorry declaration was treated as a finished proof.

Changes: removed the optional lem-weil-derived-tensor-functorial citation and its tool-use request because the direct chain-map proof already establishes the transition laws; added explicit compatibility with chain maps and their localized inverses in steps 2 and 3, closing the resolution-independence explanation; removed the corresponding unused citation from citations.json. The first worker's report and Review by NH remain intact. No statement, source hypothesis or new node was changed.

## Second reading by NH

- Item statement: checked the coefficient, quotient, torsion, perfectness, reduction, transition, normalization, unit, and cocycle clauses against blueprint node `def-weil-pbc-complete-coefficient-datum` (order 1255); PASS, including the zero quotient, empty scheme, zero complex, equal indices, and a nonflat quotient example.
- Step 1: checked the K-flat resolution, pro-etale coefficient category, and derived change-of-rings statements; PASS, and the cited statements provide the asserted model and resolution independence.
- Step 2: checked quotient powers and maps, sheaf tensor/change of rings, restriction of scalars, and the displayed generator calculation; PASS, with the elementary marking justified by direct class and chain-map calculations.
- Step 3: checked K-flat preservation and derived change of rings for both coefficient maps, including balancing, differential, and comparison formulas; PASS.
- Step 4: checked the triple-tensor cocycle and unit calculation against the explicit tensor construction and K-flat model; PASS.
- New nodes: none; B1--B7 and duplicate/Mathlib-leaf checks are vacuous, and whole-blueprint/DAG searches found no missing supporting node.
- Changes: filled the required item blueprint `from` record with its own ancestor, exact definition clauses, and empty `via`; clarified the split report's blueprint entry. No mathematical statement or proof step changed.
