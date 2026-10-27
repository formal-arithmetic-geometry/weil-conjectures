## Worker report

Item: lem-sfb-closed-immersion-unbounded-projection-formula. Group O4. Stage 1 only; 2026-10-24.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-closed-immersion-unbounded-projection-formula.json: statement, split into seven proof steps using existing nodes; statement and statement dependencies retained verbatim.
- citations.json: one entry per step/node citation, quoting the existing node statement verbatim.
- report.md: this report and signed review.

No new nodes, no new Mathlib leaves. The auxiliary create_split.py and the actual search log searches.jsonl remain sandbox research files. Nothing was written to the shared repository, launcher, or Lean source, and no compiler, Lake, or library build was run.

### Attachments

None. Searched the live WeilConjectures source for the blueprint id, closed-immersion projection terminology, the 0B55 tag, and the ordinary/derived module projection implementations. Read AlgebraicGeometry.nonempty_closedStructure_tensor_projection in AlgebraicGeometry/ClosedStructureTensorProjection.lean:132: it concerns the structure sheaf in the closed-source factor, not arbitrary E. Read AlgebraicGeometry.nonempty_qcqs_derivedProjection_iso_universes in AlgebraicGeometry/QCqsDerivedProjectionIsoUniverses.lean:57: its hE and hK hypotheses require quasi-coherent derived objects. Neither is an attachment. ClosedImmersionPushforwardExact.lean:44 proves abelian-sheaf exactness only. The étale coefficient projection formulas concern a different module category. There is no project declaration found that gives every clause of this item with its hypotheses.

### Literature and searches

WANTED: none.

Read the item's complete proof in cohomology.tex, Tag 0B55, label lemma-projection-formula-closed-immersion, including the preceding equation-projection-formula-map defining the canonical morphism by derived adjunction. It applies to all ringed-space maps homeomorphic onto a closed subset, so the scheme closed-immersion hypothesis is sufficient. No surjectivity of the structure-ring map is needed in the argument, and no quasi-coherence or Tor bound is supplied or assumed.

Read the current blueprint through literature/blueprint/latest, snapshot main-20261024, including the sk-thm-sf-ctf-stability unit and direct-images proof (3). This is a seeded structure-module supporting tool in the inherited 09US/0B55 chain, not a replacement for the constructible six-functors route. The existing blueprint.from has node=null; blueprint_refs.py ancestor returns None. I retained that metadata and the complete existing via chain, while recording the exact supporting source and blueprint purpose in split_report. No unit or chapter file is changed.

Searched the whole DAG by the exact 0B55 label/tag and relevant stalk, closed-pushforward, K-flat-resolution and pullback titles; the only existing 0B55 nodes are this item and its parent lem-sfb-relative-pseudocoherent-pullback. Ran blueprint_refs.py searches for projection formula, K-flat, closed immersion, 01AZ, 0B55, closed direct image, closed pushforward, unbounded projection, and coproduct. The exact/general closed unbounded formula has no separate blueprint match. The general qcqs projection formula requires quasi-coherence; existing closed-structure tensor nodes have a specialized first factor. I reused the smaller input nodes, rather than creating ordinary projection, pushforward-sums, or exact-module-pushforward duplicates: their few-line arguments are written in the item's steps.

All new Mathlib searches used batch2/msearch.py and were read as returned. LeanFinder's first phrasing returned closed-immersion geometry and open restriction adjunctions; its second phrasing returned ordinary flat-module tensor exactness. LeanSearch returned closed embedding and closed immersion properties. Loogle returned no projectionFormula declaration. The source grep returned only the Witt-vector projection formula and an Ehresmann-connection comment; the second grep in AlgebraicGeometry found no KFlat/IsKFlat/derivedTensor or derived-pushforward signature. These do not assert the item's formula. The exact queries and actual response summaries were appended to mathlib_searches from searches.jsonl; the prior worker's four existing search records were preserved as history/material, not represented as newly run searches. No unavailable response was called a negative result.

### Faults and limitations

The imported item had no proof. Its mathematical statement agrees with 0B55, so no statement dispute or correction is needed. The inherited null blueprint ancestor is reported above rather than replaced by an invented ancestor. The direct delivery brief requires this worker's signed review; there is no second worker or agent. The maintainer reviews the resulting delivery independently. Generic supporting facts from other units are explicitly declared in split_report.tool_uses, not as maintainer-owned top-level tool_uses.

Nothing mathematical remains unfinished at this split level. All smaller facts are existing DAG nodes, which need not already have completed Lean proofs for stage 1.

## New nodes

None (0 new nodes, 0 Mathlib leaves).

## Not duplicates

No new-node/existing-node pairs: no new node was created. In particular the ordinary projection and direct-sum comparisons were kept as explicit arguments instead of introducing new nodes for elementary consequences of the existing stalk statements.

## Review by O4

I read Stacks cohomology.tex 0B55 in full, together with Modules 01AX (lemma-i-star-exact) and 01AZ (lemma-i-star-right-adjoint), Sheaves 00AE (lemma-stalks-closed-pushforward), 0098 (lemma-stalk-pullback-modules), Section 009E on stalks of colimits, Sites Modules 03DA/03DB (lemma-abelian and lemma-limits-colimits), Cohomology 06YC (lemma-pullback-K-flat), 06YF (lemma-K-flat-resolution), 079R (lemma-tensor-product-K-flat), 079U (lemma-pullback-tensor-product), 079W (lemma-adjoint), Sites Cohomology 06YS (lemma-K-flat-resolution), and Derived Categories 015F (lemma-right-derived-exact-functor). There are no new node statements to check against a separate source. I opened and read the statement of every cited existing node; citations.json contains the actual statements used, not proof snippets or tags standing in for statements.

Step 1 uses def-weil-closed-immersion for the topological closed embedding; lem-sc-closed-immersion-pushforward-exact really states exactness for all abelian sheaves, not just a coefficient or quasi-coherent subclass. The forgetful node lem-weil-pbc-module-sheaves-colimits-forgetful is about arbitrary ring sheaves on a sheafifiable site and explicitly preserves kernels and cokernels. This justifies passing to structure modules by detecting the zero homology object. The exact-functor-derived-functor node explicitly says every unbounded complex computes the right derived functor. Thus this step proves the exactness clause rather than silently assuming it from the definition of pushforward. Identifying Z with its closed topological image is legitimate because a closed immersion is a homeomorphism onto that image.

Step 2 uses lem-pc-kflat-resolution, whose statement is for every complex on a ringed site, so the site of opens qualifies even for non-quasi-compact schemes. def-pc-derived-pullback explicitly computes on a K-flat resolution, while lem-pc-kflat-pullback-preservation states K-flatness of the actual tensor pullback for general ringed-space maps. These say different things, and both are needed: computation alone does not supply K-flatness on Z. def-pc-scheme-derived-tensor-structure gives direct-sum K-flat tensor models. The first factor A can therefore be arbitrary; no hidden K-flat assumption is put on E or i_*A.

Step 3 uses the actual sheafified tensor construction and the tensor-pullback/direct-image adjunction to construct the section map. The closed-pushforward-stalk node gives zero off the image and the scalar-restricted stalk on it, with germs and naturality. The tensor-stalk and pullback-stalk nodes both state the precise structure-ring tensor identifications and germ formulas used. I checked the ring directions: N_p is over O_{P,p}, M_z over O_{Z,z}, and the inverse multiplies u by b in O_{Z,z}. The two balancing relations make the displayed inverse well defined. This argument is the module formula itself; no new node merely restating the item's derived formula is introduced.

Step 4 uses exactly the mono and epi stalk criteria for abelian sheaves, together with the faithful exact module forgetful statement, to turn the stalk calculation into a module-sheaf isomorphism. lem-pc-stalk-direct-sums is for arbitrary sets, not finite families; lem-weil-pbc-closed-pushforward-stalks gives both cases of the comparison. The canonical sum comparison is the identity on each image stalk and zero-to-zero off it. This is a few-line consequence of those statements and needs no new lemma node. I did not use the abelian-only 01AZ statement as though it already asserted a structure-module result.

Step 5 uses def-pc-tensor-complex-sheaves for its actual differential and direct-sum convention. The degreewise map is assembled from previously proved m_{A^p,K^q} and the proved sum comparison. Checking both differential directions, including (-1)^p, is written out. This is elementary assembly from steps 3-4, not an omitted totalization comparison lemma.

Step 6 checks the point at which an arbitrary isomorphism would be insufficient. A second K-flat resolution B -> i_*A gives a comparison roof. Its tensor with K is a quasi-isomorphism because its cone is the tensor of an acyclic cone with the K-flat K. lem-pc-kflat-tensor-product ensures B tensor K itself is K-flat; that is the hypothesis needed for the second adjunction comparison. I read lem-pc-kflat-pullback-adjunction-comparison: it applies to any complex I in its target, without requiring K-injectivity or boundedness, and explicitly equates the localized ordinary transpose with the derived transpose. This is why it can be applied both to a and to the tensor map. def-pc-derived-pullback-tensor-comparison fixes the canonical tensorator by its equation on K-flat pairs; a generic assertion that pullback is monoidal would not pin down the desired map. Comparing the section formula b tensor k -> a(b) tensor i^*k identifies the derived mate with the already invertible chain map m. The result is the canonical morphism of 0B55, not just some isomorphic source and target. Step 7 only combines that identification with step 5 and the termwise computation of step 1.

I checked B-E of delivery-errors point by point. No statement-only node carries a hidden proof because none is created. Every non-elementary input is an existing node cited at the step using it; the full citations were checked as verbatim statement text. No proof of a dependency is used as if it were its statement. No new node repeats an item clause. No coefficient category is interchanged with structure modules. Direct sums are indexed by sets (the total-degree pairs are a subset of Z x Z), so no large colimit is assumed. Every non-elementary step is shorter than 2000 characters (the longest is step 6, 1595 characters); there is no long inline hidden lemma. The only elementary assembly step with citations is step 5, whose two differential equations are explicitly supplied.

Small cases: for i the identity, the stalk map and its inverse reduce to tensor balancing/unitors. For Z empty both sides are zero, and the argument includes the empty sum. For a nonreduced closed immersion, the argument uses scalar restriction and does not identify O_{P,p} with O_{Z,z}. For the closed point Spec(Z/2) -> Spec(Z), arbitrary Z/2-module M and Z-module N give exactly M tensor_Z N = M tensor_{Z/2}(N tensor_Z Z/2); this also tests a nonflat closed immersion. Arbitrarily unbounded A and K still have countable direct sums in each total degree and the same signed differential, so the proof does not truncate them. Zero objects in either factor give zero throughout. These checks preserve all hypotheses and clauses of the original item.

Corrections made during review: I rejected the tempting qcqs/QCoh projection theorem and the closed-structure special case as attachments, supplied module exactness through the stated forgetful theorem, supplied the module direct-sum argument instead of citing abelian-only 01AZ for it, and added the explicit K-flat adjunction roof to verify canonicity. The item's statement was unchanged.
