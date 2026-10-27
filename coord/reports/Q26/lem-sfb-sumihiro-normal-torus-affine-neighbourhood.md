# Stage 1 delivery: Q26

## Files written

All files below are under this item's sandbox, in dag/nodes/sec-six-functors-basics/.

- lem-sfb-sumihiro-normal-torus-affine-neighbourhood.json: item, statement unchanged, six proof steps, status split.
- lem-sfb-sumihiro-invariant-quasiprojective-open.json: statement only, unsplit; no Mathlib match after both semantic phrasings, Loogle and source grep.
- lem-sfb-normal-quasiprojective-equivariant-immersion.json: statement only, unsplit; no Mathlib equivariant immersion/linearization theorem found.
- lem-sfb-projective-invariant-boundary-ideals.json: statement only, unsplit; Mathlib vanishing ideals and ordinary projectivization actions do not supply the invariant reduced scheme closures or the universal rational subrepresentation assertion.
- citations.json: exact statement excerpts for every step citation. searches.jsonl: unmodified command log. prepare.py: sandbox-only preparation script.

Three new nodes, zero Mathlib leaves. No repository, launcher, literature, unit, or Lean file was changed. No compiler, Lake or build was run.

## Attachments

None. I searched lean/WeilConjectures by the item id, Sumihiro, invariant affine neighborhood, linearization, equivariant immersion, and projective invariant ideals. The invariant affine neighborhood theorem in AlgebraicGeometry/InvariantAffineNeighbourhoods.lean is for finite locally free descent groupoids, with a finite orbit hypothesis. It does not apply to a positive-dimensional torus. Projective charts and weight decomposition prove only pieces. No finished project declaration states this item or a new input exactly.

## Wanted literature

WANTED: H. Sumihiro, Equivariant completion, J. Math. Kyoto Univ. 14 (1974), 1--28, Theorem 1 and Lemma 8, for lem-sfb-sumihiro-invariant-quasiprojective-open and lem-sfb-normal-quasiprojective-equivariant-immersion; Corollary 2 for comparison with the item's conclusion.

WANTED: M. Brion, Algebraic group actions on normal varieties, arXiv:1703.09506v3, Introduction, Theorem 1 and Corollary 2.14, for the same two nodes. The online primary source was read at https://arxiv.org/html/1703.09506 and https://arxiv.org/pdf/1703.09506. It is not present in literature/, and nothing was downloaded into the repository. Its introduction explicitly separates invariant quasi-projective neighborhoods from equivariant immersions. Section 2.1 defines variety to mean integral, which is why the finite-disjoint-component extension is explicitly identified as agent supplied in the new nodes' sources.

## Problems found and corrected

The item had no proof; its source already correctly identified Sumihiro as absent. Its statement is true and is unchanged, including arbitrary scheme points, reducible normal schemes, rank zero, ineffective actions and positive characteristic. No STATEMENT-DISPUTED assertion is necessary.

A projective eigen-coordinate chart does not by itself prove this statement: an arbitrary immersion into that chart only yields a quasi-affine locally closed subscheme. The split instead chooses a positive-degree eigen-polynomial in the entire boundary's vanishing ideal. Its nonvanishing locus in the reduced closure has no boundary and is closed in the affine projective chart. Nor is an ambient weight decomposition sufficient: the boundary ideal has to be a rational subrepresentation. That scheme-level comparison is the third new statement, not an unproved inline transition.

The imported blueprint.from.node is null along the existing creation chain. The ancestor command also returns None. I retained that actual ancestry, extended its precise place and via data for the three new nodes, and did not invent a blueprint id. Searches over every blueprint chapter found no equivalent general Sumihiro or equivariant embedding node. The item is not the unit's key node; no realization fields were touched. I read the current latest unit and its direct-image proof, as well as the chapter and unit records; this remains a supporting normal-case tool in the already seeded concentration/alteration input, not a replacement for any unit-level direct-image step.

Nothing remains unfinished in this one-level split. The three new nodes intentionally have statements, no proofs, and join the stage-1 queue. Their source fields do not claim that Milne proves Sumihiro or that Stacks 03GL proves equivariant closure stability.

## Not duplicates

lem-sfb-sumihiro-invariant-quasiprojective-open vs lem-sfb-smooth-projective-torus-invariant-affine-cover: the existing result assumes smooth projective schemes and a torus; the new input gives invariant quasi-projective neighborhoods for general connected smooth affine groups acting on possibly singular normal finite-type schemes. The smooth projective theorem cannot produce the needed neighborhood.

lem-sfb-normal-quasiprojective-equivariant-immersion vs lem-sfb-general-flag-isolated-linear-action: the existing projective representation is only for a Borel quotient and includes a special cocharacter; the new statement treats arbitrary normal quasi-projective schemes.

lem-sfb-normal-quasiprojective-equivariant-immersion vs lem-per-equivariant-projective-envelope: the existing result is for an abstract finite group acting over a Noetherian base; it does not give a rational action of a connected positive-dimensional algebraic group.

lem-sfb-projective-invariant-boundary-ideals vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing result constructs the ideal of an already closed projective subscheme; it says nothing about actions, invariant reduced closures or rational subrepresentations. That existing homogeneous ideal realization is cited directly in item step 3.

lem-sfb-projective-invariant-boundary-ideals vs lem-per-projective-closed-subscheme-homogeneous-ideal: likewise the canonical homogeneous ideal statement has no group action or closure/boundary invariance clause; I use the equivalent existing node of this item's own unit.

lem-sfb-projective-invariant-boundary-ideals vs lem-sfb-projective-local-equation-extension: the existing node homogenizes a local equation after a coordinate power; it does not preserve an algebraic group action or identify stable boundary degree representations.

lem-sfb-projective-invariant-boundary-ideals vs def-sfb-projective-coordinate-hilbert-polynomial: that node only defines coordinate degree quotients and a numerical polynomial predicate, not invariance under group actions.

lem-sfb-projective-invariant-boundary-ideals vs lem-sfb-homogeneous-quotient-chart-kernel: the existing degree-one localization kernel calculation has no action, closure, boundary or subrepresentation assertion.

lem-sfb-projective-invariant-boundary-ideals vs lem-sfb-projective-field-coordinate-euler-polynomial: that node concerns Euler/Hilbert polynomials of a closed projective scheme, not group stability of its boundary ideals.

lem-sfb-projective-invariant-boundary-ideals vs lem-per-equivariant-projective-envelope: an equivariant completion for a finite abstract group is not the reduced closure and universal polynomial coaction of a smooth algebraic group already acting linearly.

I also searched all DAG statements/titles and the blueprint for quasi-projective neighborhoods, normal schemes with actions, equivariant immersion, homogeneous ideal, invariant closed, Sumihiro, and projectivization. The weight decomposition, Proj charts, and ideal realization already exist and were reused. No new elementary lemma or clause of the item was made into a node. The two Sumihiro inputs apply to connected affine groups for which the affine-neighborhood conclusion is generally false, so neither merely renames the item's torus-affineness conclusion. The third is a normality-free scheme-level equivariance comparison, not the affine-neighborhood assertion.

## Review by Q26

I read delivery-errors B--E in full (both the current and the merged copy) with the item, the three new statements, and the cited statements open. For sources I read Milne's Theorem 12.12 and Remark 12.13 (weight decomposition), Definition 13.45 and Lemma 13.46 (linear torus affine charts), and the projective action discussion of Section 7. I read Stacks constructions.tex, label lemma-closed-in-projective-space, Tag 03GL, including its homogenization proof, and the standard-open chart construction, Tag 01M4, label lemma-standard-open. I read properties.tex, Tag 0357, label lemma-normal-locally-finite-nr-irreducibles, to check the normal-component extension used to formulate the new inputs faithfully. Milne Corollary 1.18 explains reduced closed subvarieties being determined by geometric points; it does not alone supply the universal closure/ideal coaction statement, so I made that a separate unsplit lemma. For the two genuinely deep Sumihiro statements, the paper is missing and is marked WANTED; Brion's online primary source confirms the two separate assertions and their hypotheses. The item's proof_origin is agent, not document.

Step 1 uses precisely the lattice-torus projection statement for smoothness and the Laurent coordinate domain. Affineness and finite type follow from the displayed Laurent presentation; the zero prime gives irreducibility and thus connectedness directly. The new invariant-quasi-projective node assumes a smooth connected affine finite-type group and a normal separated finite-type scheme, all checked here. Its conclusion includes normality, separation and finite type of the neighborhood; the step does not infer these from an unspecified open immersion. This avoids a hypothesis mismatch on the next input.

Step 2 uses exactly the new equivariant immersion node for the representation and immersion of W; it neither assumes a projective X nor faithfulness. The boundary node is applied to a reduced locally closed scheme (normal local domains imply reduced), and to the smooth torus already established in step 1. Its statement explicitly gives the reduced closure, the open identification of W, the invariant boundary and the finite-dimensional rational representation on every I(B)_d. I am not extracting any unstated construction from the proof of another node. The lemma is deliberately retained as a real supporting input: invariance must hold on universal group-scheme points and survive tensoring with arbitrary algebras, which ordinary preservation on F-points or the bare definition of a homogeneous ideal does not state.

Step 3 reads the actual statement of lem-sfb-projective-closed-subscheme-homogeneous-ideal: its I_d is defined by the same chartwise vanishing as the new boundary lemma, and its conclusion realizes the boundary as Proj(S/I). The variable B in that existing node denotes the polynomial ring; the item's B denotes a boundary, so the step renames that ring S consistently. The prime-ideal argument and positive-degree correction are written out from def-pc-proj; no separate prime avoidance or closed-point theorem is used. This works for a nonclosed point, and also for empty boundary: multiply the degree-zero constant by a coordinate outside the prime when necessary.

Step 4 applies the existing split-torus representation weight-decomposition statement to I(B)_d itself. It requires a field, a finite-dimensional vector space and a group-scheme representation, all supplied by the hypotheses and step 2. The decomposition's eigenvector assertion holds after every commutative algebra extension. The prime is closed under finite sums, so at least one component of f is nonzero at the selected arbitrary point. No numerical torus character formula, extreme-weight assumption, or fixed-point hypothesis is used.

Step 5 uses prop-nagata-proj-standard-open only for its stated affineness of D_+(h), with d>0 verified in step 3 and preserved in step 4. The scheme Z is actually closed, by the boundary lemma, and def-weil-closed-immersion explicitly gives the affine quotient description of its inverse image. Equality with U uses the open-scheme identification W=Z minus its boundary, not merely a set-theoretic factorization through a closed subscheme. This corrects the tempting but false shortcut of treating every quasi-affine chart as affine.

Step 6 uses the previously obtained representation and eigenvector identities in the explicit contragredient convention. The identity is h(rho(g)v)=chi(g)^(-1)h(v), so the scalar is a unit in every test algebra, including algebras with nilpotents. Checking local generators of the universal line proves invariance of the whole open subscheme, not just of F-points. Open restrictions give the factorization; an open immersion is monic because maps into its open restriction are determined by their composites. Thus unit, associativity and equivariance restrict as claimed. This is an elementary calculation, not a hidden comparison lemma.

I tested the statements on the empty scheme, trivial group/rank-zero torus, zero-dimensional normal schemes, reducible disjoint normal components with an ineffective action, a singular normal affine torus variety, and a normal open subvariety of projective space with nonempty boundary. The new immersion statement requires a nonzero V even for empty X, where a trivial one-dimensional V works. The boundary statement allows empty W or B and disconnected smooth G; all degree pieces are finite because they are subspaces of a finite-dimensional polynomial degree. Smoothness is retained on the boundary input so products with reduced varieties stay reduced over the perfect field; it is not silently dropped. In characteristic p the argument uses the diagonalizable torus representation statement, not averaging or characteristic-zero complete reducibility. No new statement needs X smooth, irreducible, projective or its action effective. No step exceeds 2000 characters, and I checked that no shorter step hides a non-elementary transition: the equivariant closure/ideal comparison was extracted for that reason.

The only declared generic off-unit proof tool is lem-trf-split-lattice-torus-projection, for Laurent torus smoothness and the domain property. The Proj chart theorem is declared as a generic tool as well; the homogeneous ideal theorem was switched to the existing version in this unit. Neither changes the fixed chapter route. New statement dependencies introduce their notions explicitly with definition references and inline meanings for quasi-projectivity, rational representation and invariance. Each new node is statement-only, has exact executed search texts and honest outcomes, null mathlib_match, complete created and blueprint data, and none Lean audits. I read the search hits: the closest projective vanishingIdeal_closure and IdealSheaf.map_vanishingIdeal are ordinary vanishing-ideal statements and do not produce the universal algebraic-group representation needed. They are not one-line specializations of any new node. Each citation quote was checked as a literal substring of its node statement.

## Validation

The server-only review_split check passed. The required deliver.py --no-push completed and printed OK (not pushed), preflight passed, at 56b1457f45e. This dry run includes check_dag, review_split, the search-log gate and literal citation validation. No local copy of a server checker was run.
