# prop-weil-pbc-strict-local-exchange

## Files written

- dag/nodes/sec-proper-base-change/prop-weil-pbc-strict-local-exchange.json: statement, split using existing canonical-germ and comparison nodes; no Mathlib match.
- citations.json: verbatim statement quotations for every step citation.
- No new nodes; no Mathlib leaves; no unit record change (this is not the unit's key node).

## Attachments

None. Read StrictHenselian.lean lines 173–264 in the read-only slopmaster2 checkout. AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal has sorry at line 224, and its docstring explicitly describes its existential-equivalence formulation as weaker than the blueprint's canonical one. The isIso theorem proves the second clause but depends on that sorried theorem. Neither is a complete attachment.

## WANTED

None. Used the locally available Stacks sources.

## Statement clarification — STATEMENT-DISPUTED

The imported text names neither a sheaf nor a cohomological degree: as written “the cohomologies” and the exchange component have no coefficient argument, so they cannot be typed as a definite map. Made explicit the intended torsion abelian sheaf F and q ≥ 0, as in Stacks 095T and unit sk-thm-p1(ii)-(iii). This is the abelian derived exchange defined by the cited definition. No identification with arbitrary module coefficient derived categories is asserted. The existing Lean theorem handles torsion Λ-module sheaves and only existential equivalences; it is not an exact statement binding for this node. Both the stronger canonical identification and the residue-isomorphism conclusion are retained.

The previous proof's two existential comparison interfaces only promise some equivalences, so their statements do not establish canonicality (C4). Its last sentence also called an existential statement “unchanged”, contrary to the blueprint. Replaced those citations with existing canonical global-germ lemmas, not stronger claims about their existential statements.

## Blueprint and duplicate search

Searched all DAG statements and titles for strict-local, canonical germs, cohomology pullback, 03QO and theorem-higher-direct-images; ran tools/blueprint_refs.py search for strict.local, pullback, and Strict-local projective-line exchange. The exact title search finds only this blueprint node. Reused the existing germ, exchange, functoriality, torsion, inverse-image and projective-line comparison nodes. No new node is needed; the explicit residue square and final conjugation are elementary steps, not new lemmas. No same_as alternative was found.

## Not duplicates

No new nodes.

## Review by NG

Read the item's original blueprint file, its unit and chapter, Stacks etale-cohomology.tex 03QO (lemma-vanishing-etale-cohomology-strictly-henselian) and 095T (theorem-proper-base-change), including the resolution comparison and final stalk-map paragraphs. Also read cohomology.tex 01F8 (lemma-functoriality) and sites-cohomology.tex 08J6 (remark-before-Leray). The source proves the prime-coefficient comparison directly; the reused projective-line comparison node explicitly supplies the general torsion abelian case by devissage. This is not a new claim that the displayed prime-coefficient source alone already proves arbitrary coefficients.

For step 1 I checked def-nagata-projective-space-base-change: it is the product with a fixed projective scheme, so equality and the inverse in step 5 follow by equality of the two projections. The residue identity holds because both ring maps send a to the class of φ(a). The inverse-image-composition node supplies the coefficient comparison, compatible with units; it is not being used as a statement about cohomology.

For step 2 I opened the full statements of def-weil-pbc-derived-global-germ, lem-weil-pbc-strict-local-global-germ-iso, lem-weil-pbc-derived-global-germ-exchange and lem-weil-pbc-cohomology-pullback-derived-unit. The first defines the canonical derived maps and exact-stalk identification; the second supplies natural isomorphisms before derivation, not merely arbitrary pointwise bijections. Applying derivation and homology to these maps and their inverses keeps their inverse identities. The third gives exactly their exchange equation without properness or torsion; the fourth identifies its unit/Leray arrow with the specified cohomology pullback. A local map of strictly henselian rings and the closed residue-field point meet the hypotheses. This repairs the canonicality gap rather than borrowing the proofs of the existential-equivalence nodes.

For step 3 the inverse-image-stalk-germ statement explicitly identifies the requisite stalks, and the torsion characterization explicitly equates torsion stalks with torsion sheaves. The two comparison applications thus have torsion abelian coefficients, strictly henselian bases and exactly the projective lines required. The off-unit torsion characterization is a generic tool; its acceptance is for the maintainer to record, not this delivery.

For step 4 the functoriality node's clause 4 states the composition law with its coefficient isomorphism. Applied to the two equal composites of step 1 it gives the precise restriction-square equality used, after which the three displayed equalities are substitution. For step 5 the same clause includes the identity law and therefore gives the inverse of pullback along a scheme isomorphism; this avoids using an unnamed cohomology invariance theorem. All quotes in citations.json are verbatim statements, and no step uses an internal construction available only in a cited proof.

Checked the empty coefficient sheaf, q=0, identity A→A, and the case A and B already separably closed fields: the two restrictions become identities in the field case and the formula is precisely pullback. No noetherian, finite-type-base, prime-to-characteristic, residue-isomorphism, or proper-base-change theorem is used to obtain the first clause. The residue-isomorphism hypothesis is used only for step 5. Recursive dependency searches of the new canonical-germ route do not reach this item, so there is no circular use of this result. Reviewed delivery-errors B–E: self-contained coefficient data, no hollow/new nodes, exact cited statements, no moved clauses, no Mathlib claim from unavailable services. Actual Mathlib searches are logged; LeanFinder returns etale ring maps or topological stalks, Loogle has no match, the grep returns a manifold restriction definition, and LeanSearch is recorded unavailable.

## Unfinished work

None at this one-level split. Existing cited nodes retain their own obligations. No Lean was written or compiled, and no delivery was pushed.

## Second reading by NG

Statement: checked the original blueprint proposition, unit sk-thm-p1(ii)-(iii), Stacks 095T (theorem-proper-base-change, strict-henselian and final stalk paragraphs), and 03QO (lemma-vanishing-etale-cohomology-strictly-henselian); PASS. The coefficient/degree clarification faithfully supplies the missing arguments, and the canonicality and residue-isomorphism clauses are retained. Stacks prints the prime-coefficient comparison; the existing comparison node explicitly states the torsion extension used here.

Step 1: opened def-nagata-projective-space-base-change and lem-weil-pbc-inverse-image-composition, clauses 1–2; PASS. The quotient identity and equality of the product projections give the square, and the unit-compatible composition maps give its coefficient isomorphism.
Step 2: opened def-weil-pbc-derived-global-germ, lem-weil-pbc-strict-local-global-germ-iso, lem-weil-pbc-derived-global-germ-exchange, and lem-weil-pbc-cohomology-pullback-derived-unit, clauses 1–2, against 03QO, 095T, 01F8 (lemma-functoriality), and 08J6 (remark-before-Leray); PASS. Natural germ isomorphisms and their inverses remain inverse after derivation and homology; the exchange identity is for these canonical maps. Strict henselianity makes the residue fields separably closed, and locality puts the image geometric point over the closed point.
Step 3: opened lem-weil-pbc-inverse-image-stalk-germ, lem-weil-pbc-torsion-sheaf-characterizations, and prop-weil-pbc-p1-strict-henselian-comparison; PASS. Their statements give precisely the stalk identification, the two directions of the torsion criterion, and the actual restriction isomorphisms in all nonnegative degrees; no proof-internal construction is used.
Step 4: opened lem-weil-pbc-cohomology-pullback-functorial, clause 4, and the composition isomorphisms already cited in step 1; REPAIRED/PASS. Wrote gamma explicitly as the inverse of one composition isomorphism followed by the other, and wrote both composition equalities before cancelling. The final element calculation proves the required canonical conjugation.
Step 5: opened def-nagata-projective-space-base-change and lem-weil-pbc-cohomology-pullback-functorial, clause 4; PASS. Product projections verify the scheme inverse, and composition/identity laws give inverse cohomology pullback with its coefficient identifications. Conjugation by e1 and e2 then proves invertibility.
New nodes: none; B1–B7 and the independent Mathlib-leaf search requirement for new nodes are vacuous. Searched the existing DAG for 03QO, 095T, global-germ and strict-local; the split reuses existing statements and creates no duplicate or restatement node.

Edge cases checked: F=0 gives zero groups and their unique isomorphisms; q=0 gives the same section/germ square; A=B and the identity ring map give identity pullback; separably closed fields make closed-fibre restrictions identities. Local rings here have residue fields, so the zero ring/empty spectrum is outside the hypotheses. No noetherian or residue-isomorphism assumption is used before step 5. Recursive statement/proof-dependency traversal from every cited node does not reach the item. Read StrictHenselian.lean lines 173–264 without compiling: the existential comparison is weaker and contains sorry, so no closed attachment is justified.

Changes: expanded step 4's coefficient transport into the explicit composition-map calculation (E5); removed the worker-owned split_report.tool_uses entry, because acceptance of the off-unit torsion-characterization tool must be recorded by the maintainer (C8). That generic criterion is needed solely to check the inverse-image torsion hypothesis; no unit-specific result replaces it. Citations remain verbatim and accurate because no citation was changed. Preserved the first worker's review and statement-dispute explanation. No Lean or live-project files were written.
