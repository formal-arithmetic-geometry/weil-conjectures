# Worker report — Q30

1. Files written: `dag/nodes/sec-smooth-purity/thm-exc-curve-open-constructible-general.json` (existing statement, split; Mathlib no match); `dag/nodes/sec-smooth-purity/lem-exc-affine-strict-local-ring-comparison.json` (new statement-only, unsplit; Mathlib no match); `citations.json` (40 exact statement quotations); and this report. One new node and no new Mathlib leaves. Preparation scripts and the archived earlier report remain sandbox-only.
2. Attachments: none. The retained source search was checked again by item tag, recorded declaration, and strict-local/curve/direct-image concepts in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. There is no exact completed project declaration for the item or the new comparison. `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar` in `SixFunctors/Etale/Derived/Stability/DirectImage.lean:81` has `sorry` at line 87; its wrappers are not closed attachments. The item's stage-2 Lean record is preserved verbatim.
3. WANTED: none for this repair. The existing excellence node remains a black-box dependency; its own recorded external-literature requirement is not asserted resolved here.
4. Repair: the returned 2711-character local step hid the geometric/algebraic strict-local comparison, finite-field closure argument, and local dimension comparison. The previous retained attempt merely separated that text into paragraphs. This repair extracts the first argument into a new theorem interface, cites the existing finite-field separable-closure Mathlib leaf for the second, and cites the existing affine-stalk localization and scheme-dimension theorems for the third. The original seven-step route and the other steps are retained, with their cross-references renumbered. Existing excellence, strict-henselian quotient and strict-henselization dimension nodes remain in use. Double-escaped TeX in proof text was normalized. The statement, Lean record, blueprint import metadata, unit and chapter are unchanged.
5. Unfinished: the new comparison is deliberately statement-only, for its own later split. There is no unfinished work in this one-level repair.

## Source and route


Read the chapter record `sec-smooth-purity`, unit `sk-prop-a1-kummer` including all five steps, and the current statement and both proof paragraphs in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/thm-exc-curve-open-constructible-general{,.proof}.md`. The current statement agrees with the inherited item. The item is a supporting general-curve constructibility computation, not the unit's key statement, so its realization record is left alone. The proof keeps the blueprint's independent low-dimensional route: degree zero, dimension vanishing, strict-local branches, finite first Galois cohomology, and the finite boundary stratification. It does not replace that computation by the general finite-type constructibility theorem.

Read Stacks `etale-cohomology.tex` Tag 03Q9 (`theorem-higher-direct-images`), Tag 04HX (`lemma-describe-etale-local-ring`, including its affine residue-triples proof), Tag 03SI (`proposition-topological-invariance`), Tag 03QT (`theorem-equivalence-sheaves-point`) and the adjacent sections/invariants discussion; read `more-algebra.tex` Tag 06LK (`lemma-henselization-dimension`). Checked the tag-to-label map. All other inputs are existing DAG nodes, whose complete statements and source records were opened; the split uses their statements, not assertions hidden in their proofs.


For the new comparison I read Stacks `etale-cohomology.tex`, Tag 04HX (`lemma-describe-etale-local-ring`), its statement and complete affine-residue-triple proof, and `algebra.tex`, Tag 04GW (`lemma-strict-henselization-different`), including both colimit descriptions and their pointings. The argument identifies the actual pointed-neighbourhood colimit over an arbitrary scheme with the pointed algebraic strict henselization at the specified affine prime. All comparison data are specified: the chart ring map, chosen relative separable closure, defining algebraic colimit cocone, structural-map square and residue identification. This is a general comparison theorem, with no curve, finite-field, constructibility or cohomology hypothesis; it is strictly smaller than the item. Its proof is not hidden inside its statement. A future split can use affine-neighbourhood cofinality, the existing residue-triple equivalence, prime-localization of pointed diagrams, and colimit uniqueness. The structural square follows on the chart leg; the two residue maps agree on every pointed leg.

For the newly used existing interfaces I also read Stacks Tag 04MU (`properties-lemma-dimension`) and Tag 06LK (`more-algebra-lemma-henselization-dimension`), and the literal statements of `lem-weil-pbc-affine-open-stalk-localization`, `lem-pc-scheme-dimension-local-rings`, and `lem-sfb-finite-field-separable-closure-algebraic`. I read the latter's actual Mathlib declarations: `IsSepClosure.isAlgClosure_of_perfectField` in `Mathlib/FieldTheory/IsSepClosed.lean:244` and `PerfectField.ofFinite` in `Mathlib/FieldTheory/Perfect.lean:308`.

## Mathlib and existing-node searches

All inherited item searches and their actual `searches.jsonl` results are retained. The initial dry run at resumption completed with OK (not pushed), head 594277e423; that receipt tested the retained attempt, before this extraction. No duplicate delivery command was started while it ran.

For the new node, `msearch.py Q30 thm-exc-curve-open-constructible-general` ran two LeanFinder phrasings (strict localization in an affine chart; canonical comparison of pointed-neighbourhood colimits with algebraic strict henselization), Loogle `StrictHenselization, AlgebraicGeometry.Scheme`, grep `strictHensel|StrictHensel|strict.henseli|strict.locali` in AlgebraicGeometry, and a LeanSearch inverse-limit phrasing. Both semantic results were read: they give ordinary affine stalk/localization and residue-field maps, or standard-etale homs. Loogle reports an unknown strict-henselization identifier and grep has no hits. LeanSearch gives profinite limits, henselian locality and an ordinary closed-point stalk isomorphism. None supplies the comparison. The new node records exactly those five logged searches, with their actual results. No unavailable search is reported as absence.

A separate field-algebra search found `IsSepClosed.isAlgClosed_of_perfectField` and `IsSepClosure.isAlgClosure_of_perfectField`; a whole-DAG search then found the existing, more precise Mathlib leaf `lem-sfb-finite-field-separable-closure-algebraic`. I use that node instead of creating a field-closure lemma. Likewise the DAG already contains the exact affine-stalk and scheme-dimension interfaces; no new dimension lemma was created. Blueprint searches included `separable closure`, `strict henselization`, `strict-local`, `etale local ring`, `residue triples`, and `strict henselization of the local`. None states the new comparison with its specified chart, structural map and residue compatibility. `blueprint_refs.py ancestor` identifies the item itself as ancestor; the new node has its precise proof-place and empty via list. Its `same_as` is empty.

## Review by Q30

I re-read delivery-errors B–E and repaired the substantive return, rather than only shortening paragraphs. Every new statement is self-contained, its definition dependencies are actual definition nodes, and the new node has no proof or proof dependencies. It states a ring/scheme comparison, not the item's constructibility conclusion or a degree-one clause of it. All cited statements were read, and the 40 quotations in `citations.json` are their literal statements.

Step 1 retains the Noetherian/qcqs preparation: local finite type over a field gives local Noetherianity; quasi-compactness is part of finite type; the Noetherian-open theorem makes the open immersion quasi-compact and its diagonal is an isomorphism. The direct-image definition covers constant-ring module sheaves and an injective-resolution representative. Degree-zero constructibility and vanishing above one have the same field, coefficient and dimension hypotheses as here. Negative degrees vanish for a resolution of a degree-zero sheaf.

Step 2 retains the elementary boundary argument. The two cited topology statements supply finite irreducible decompositions and generic points. Density puts each component's generic point in U; a non-singleton boundary component gives a strict chain of length two in T. The dimension definition rules that out. This works when U is empty, non-dense, or misses whole components.

Step 3 retains the vanishing off the boundary. The inverse-image theorem is exact on the actual constant-A module categories and identifies its underlying counit with the abelian counit. The cited open-immersion theorem makes that counit an isomorphism. Applying it degreewise to a resolution is a chain isomorphism by naturality. Outside the closure the direct-image formula is termwise zero because the fibre products are empty. No unproved derived counit is assumed.

Step 4 now only computes the strict-local stalk. The forget-comparison is for arbitrary constant commutative coefficients and every degree; the stalk theorem is for torsion abelian sheaves and qcqs morphisms. The coefficient annihilator and step 1 supply exactly those hypotheses. No local-algebra identification is performed inline here.

Step 5 now cites the new comparison for the actual affine chart and prime, the fixed geometric point and the relative separable closure inside Omega. Its statement supplies the spectrum identification over T, locality, strict henselianity and the specified residue field. The old chain of informal identifications has been removed. The existing closed-fibre-backward statement puts precisely this closed point over t, as needed to exclude it from the pulled-back open. I checked the comparison against Tag 04HX and 04GW, including the orientation of Spec(theta): Spec of the algebraic model maps to the chosen geometric strict localization.

Step 6 now cites the existing finite-field closure leaf, with base field kappa(t), not k. The closed-point-field theorem applies because t is closed and T is finite type over k. If k is finite then kappa(t) is finite; its specified separable closure is covered by that leaf. If k is algebraically closed, the finite residue extension and the algebraic separable closure equal k by linear minimal polynomials. These are the two stated ground-field cases, both in positive characteristic. The perfectness/Frobenius subargument is no longer inline or marked elementary.

Step 7 cites explicit interfaces for each non-elementary local-algebra fact. Excellence applies to the same finitely generated D and its prime p and explicitly covers both the strict henselization and its nilradical quotient. The quotient theorem applies because every nilpotent lies in the maximal ideal and preserves exactly the residue field used in step 6. The affine-stalk theorem gives D_p isomorphic to O_(T,t); the scheme-dimension supremum theorem bounds that particular stalk by dim T; strict-henselization dimension applies to the local ring D_p. Only the elementary quotient observation remains written out: prime ideals all contain the nilradical, inverse images preserve strict prime chains, and the quotient is reduced. It introduces no new normality, regularity, separatedness or dimension-one assumption.

Step 8 retains reduction and branch selection. The cited reduction theorem includes arbitrary base change, and the topos-invariance statement explicitly gives invariance of abelian cohomology. The chosen closed point lies over t, so the pulled-back open excludes it. The zero-dimensional reduced local case is a field and gives an empty open. Otherwise the branch theorem has all its hypotheses from steps 5–7: reduced, excellent, one-dimensional, local, strictly henselian and algebraically closed positive-characteristic residue field. The open can select only a subset of branches; it need not meet them all.

Step 9 retains finite branch cohomology. The finite-coproduct theorem gives exactly the cohomology product. The explicit constructible-module finite-stalk theorem, transported by the inverse-image stalk theorem, gives finite fibres on each field. The field/Galois equivalence is an exact equivalence compatible with sections, sufficient to transport injective lifting problems and resolutions to derived invariants. Module/abelian cohomology forgetting is explicitly cited. The finite part of the DVR-Galois theorem applies with ell different from the common residue characteristic, and the product is finite even when there are no selected branches.

Step 10 retains the final point-stratum argument. The inverse-image stalk theorem and field/module equivalence give a finite continuous module at each point. The intersection of finitely many element stabilizers is an open normal action kernel; finite-transitive Galois-set classification gives a finite separable extension with that stabilizer and the separable-extension theorem makes it an etale cover. Its action is trivial, so the module sheaf is constant on that cover. The constructible-subset definition covers finite locally closed partitions in a Noetherian space, and the constructible-sheaf definition is exactly the resulting finite lisse partition.

For the new comparison, I checked Spec of a field, the identity chart, replacing a chart by a smaller affine neighbourhood, a nonclosed prime, a geometric point with a larger algebraically closed overfield, and nonreduced chart rings. No finiteness, perfectness or dimension assumption is needed. The specified K is only a separable closure in general, never silently identified with Omega. For the item I retained the checks of empty T, U empty, j identity, zero-dimensional T, nonreduced and reducible curves, selected branch subsets, zero coefficient ring, and negative q. The unchanged item statement and Lean record were compared literally to the current shared repository. The final ten steps have lengths 993, 1007, 1086, 519, 651, 579, 821, 1468, 1420 and 1641 characters; there is no non-elementary proof step over 2000 characters. More significantly, the three returned hidden comparisons now have named theorem interfaces.

## Not duplicates

The finite-field closure and dimension facts are reused, not created. The new comparison packages the geometric-to-algebraic model identification with the specified chart prime, relative residue closure and structural/residue compatibility. It is not a new cohomology or constructibility theorem. Same-tag pairs are distinguished below.

lem-exc-affine-strict-local-ring-comparison vs def-sc-ring-strict-henselization: the existing node defines ring strict henselization relative to a chosen separable residue closure; the new node proves a comparison of the two separately defined geometric and algebraic objects.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-etale-localization-separable-closure: the existing statement is compatible residue embedding after etale localization is a separable closure; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-etale-triple-strict-henselization-identification: the existing statement is a strict henselization triple has the same strict henselization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-etale-triples-colimit-is-strict-henselization: the existing statement is colimit of residue triples is the strict henselization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-pointed-etale-essentially-small: the existing statement is pointed etale algebras are essentially small; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-pointed-etale-filtered: the existing statement is pointed etale algebras form a filtered category; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-pointed-etale-small-filtered: the existing statement is pointed etale algebra category is essentially small and filtered; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-ring-strict-henselization-local-maximal-ideal: the existing statement is local structure of a ring strict henselization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-strict-henselization-comparison: the existing statement is pointed-colimit comparison for an etale localization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-strict-henselization-dvr: the existing statement is strict henselization at a point with dvr local ring; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-strict-henselization-triples-presentation: the existing statement is compatibility of pointed-algebra and residue-triple strict henselizations; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs compatible-strict-henselization-core-data: the existing statement is compatible strict henselization core data without final residue square; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs compatible-strict-henselization-core-existence: the existing statement is strict henselization ring and residue existence; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs compatible-strict-henselization-residues-core: the existing statement is core compatible strict henselization data; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs def-weil-pbc-etale-residue-triples: the existing node defines the category of étale algebras with a prime and a residue-field embedding; the new node proves a comparison of the two separately defined geometric and algebraic objects.

lem-exc-affine-strict-local-ring-comparison vs def-weil-pbc-relative-separable-closure: the existing node defines separable algebraic closure of a field inside an extension; the new node proves a comparison of the two separately defined geometric and algebraic objects.

lem-exc-affine-strict-local-ring-comparison vs def-weil-pbc-strict-henselization-point-evaluation: the existing node defines canonical geometric-point evaluation of the neighbourhood ring colimit; the new node proves a comparison of the two separately defined geometric and algebraic objects.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-compatible-strict-henselization-residue-image: the existing statement is containment of compatible strict-henselization residue images; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-compatible-strict-henselization-residue-lift: the existing statement is lift specified residue embeddings between fixed strict henselization models; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-compatible-strict-henselization-residue-polynomial: the existing statement is separable polynomial for a compatible strict-henselization residue element; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-compatible-strict-henselization-residue-separability: the existing statement is separability of compatible strict-henselization residue elements; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-algebra-residue-field-separable: the existing statement is residue field extensions of an etale algebra are finite separable; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-chart-essentially-surjective: the existing statement is essential surjectivity of a compatible affine chart functor at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-chart-full: the existing statement is fullness of a compatible affine chart functor at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-chart-functor-construction: the existing statement is construction of the affine chart functor with ring and point formulas at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-chart-residue-triples-equivalence: the existing statement is affine chart pointed neighbourhoods are equivalent to residue-field triples at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-local-ring-triples: the existing statement stops at the geometric-neighbourhood/residue-triple colimit comparison; the new one identifies it with a chosen algebraic strict henselization and specifies the structural and residue squares.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-colimit-localization: the existing statement is localization properties of the etale residue colimit; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-colimit-polynomial-lift: the existing statement is polynomial lifting for etale residue colimit; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-colimit-simple-roots: the existing statement is simple roots lift in the etale residue colimit; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-colimit-surjective: the existing statement is the etale residue colimit maps surjectively to k; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-filtered-colimit-colimit: the existing statement is existence of the etale residue triples ring colimit; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-filtered-colimit-filtered: the existing statement is filteredness of etale residue triples over an arbitrary field; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-etale-triples-filtered-colimit: the existing statement is filtered colimit of etale residue triples; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-p1-compatible-strict-henselization-residues: the existing statement is compatible strict henselizations with integral geometric residue maps; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink: the existing statement is shrinking a pointed etale neighbourhood to an affine open around the point; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-affine-chart-ind-etale: the existing statement is strict henselization is ind-etale over an affine chart; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-chart-maximal-ideal: the existing statement is maximal ideal and structural map in an affine strict-henselization chart; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-closed-fiber-backward: the existing statement is the closed point lies over the distinguished point; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-closed-fiber-forward: the existing statement is no non-closed point in the distinguished fibre; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-closed-fiber: the existing statement is the singleton distinguished fibre of a strict henselization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-functoriality: the existing statement gives geometric local/residue structure and maps between geometric strict localizations; it does not identify them with a chosen algebraic strict-henselization colimit at the chart prime.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-local-structure: the existing statement is local structure of the chosen strict-henselization colimit; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-point-evaluation-comparison: the existing comparison ends at a residue-triple cocone and controls evaluation in Omega; the new comparison ends at the algebraic strict henselization of D_p and identifies the specified residue field K.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-point-evaluation-image: the existing statement is pointed evaluation lands in the relative separable closure; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-point-evaluation-pointed: the existing statement is pointed evaluation coprojection equation; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-point-evaluation-properties: the existing statement is surjectivity of canonical pointed evaluation; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-pointed-map-core: the existing statement is residue map with surjective kernel; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-pointed-map-factorization: the existing statement is pointed factorization for the residue map; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-pointed-map: the existing statement is surjective pointed map from the neighbourhood colimit to the relative separable closure; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-residue-separable-model: the existing statement is separable residue extension of a strict-henselization model; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-weil-pbc-strict-henselization-triples: the existing statement describes the algebraic triple-colimit local structure; it does not identify an arbitrary scheme’s actual chosen geometric ring and structural map with the algebraic model.

lem-exc-affine-strict-local-ring-comparison vs split-etale-chart-functor: the existing statement is affine chart residue triples indexing categories admit an equivalence at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs split-etale-chart-ring-iso: the existing statement is affine chart equivalence carries global sections to triple rings at the indexing-category or ring-diagram level; it does not state the geometric/algebraic strict-henselization comparison or its structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-affine-strict-henselization-structural-flat: the existing statement is flatness of the canonical affine strict henselization structural ring map; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-etale-triples-localized-strict-henselization: the existing statement starts with an algebraic residue-triple cocone and supplies a localized algebraic structure; the new one compares the actual geometric neighbourhood ring over any affine chart with a prescribed algebraic model and both structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-geometric-strict-henselization-local-presentation: the existing statement has affine base and existential prime/residue model; the new one fixes the prime supplied by a specified chart of any scheme, the relative closure inside Omega, and an isomorphism to a chosen algebraic model with its residue map.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-pointed-etale-quotient-comma-refinement: the existing statement is common successors in pointed quotient comma categories; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-regular-divisor-strict-local-limit: the existing statement is pointed regular strict local ind-etale limit of a divisor; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-strict-hensel-divisor-quotient-presentation: the existing statement is algebraic strict henselization presentation of a divisor quotient; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs lem-sbc-strict-henselization-module-fibre-factorization: the existing statement is module stalk comparison and geometric-fibre restriction factorization; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

lem-exc-affine-strict-local-ring-comparison vs new-def-sbc-etale-triples-prime-localization-cocone-relation: the existing statement concerns compatible cocone legs across prime localization for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-localized-core: the existing statement starts with an algebraic residue-triple cocone and supplies a localized algebraic structure; the new one compares the actual geometric neighbourhood ring over any affine chart with a prescribed algebraic model and both structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-cocone-equiv: the existing statement concerns natural equivalence of pointed-etale cocones across prime localization for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-cocone-extension: the existing statement concerns unique extension of a global cocone across prime localization for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-cocone-restriction-exists: the existing statement concerns existence of compatible restriction of a local cocone for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-cocone-restriction-unique: the existing statement concerns uniqueness of compatible restriction of a local cocone for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-cocone-restriction: the existing statement concerns unique restriction of a local cocone across prime localization for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-comparison: the existing statement concerns ring-colimit comparison across prime localization with fixed algebra structures for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-compatible-map-exists: the existing statement concerns compatible map into a prime-localized pointed triple for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization: the existing statement concerns cocone-leg extension and morphism factorization for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing: the existing statement concerns affine model pointing compatibility for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-structure: the existing statement concerns affine model structure descent for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model: the existing statement concerns affine model data for component extension for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux: the existing statement concerns affine model and factorization data for a component extension for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-exists: the existing statement concerns existence of a compatible local component leg for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible: the existing statement concerns existence of a compatible descended affine model for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi: the existing statement concerns the descended compatible map is an epimorphism for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux: the existing statement concerns existence of an epimorphic pointed affine model for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique: the existing statement concerns uniqueness of a compatible local component leg for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs new-lem-sbc-etale-triples-prime-localization-component-extension: the existing statement concerns a unique compatible leg on one local pointed etale triple for algebraic pointed diagrams; the new one concerns the chosen ring of an arbitrary scheme’s geometric strict localization and the chart structural/residue maps.

lem-exc-affine-strict-local-ring-comparison vs lem-sc-field-higher-direct-image-stalk: the existing statement is higher direct image stalk over a field via algebraic closure; it does not assert the specified affine-chart isomorphism between the geometric ring and a chosen algebraic strict henselization of D_p with its structural and residue compatibility.

