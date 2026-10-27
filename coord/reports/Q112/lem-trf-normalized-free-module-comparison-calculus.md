# Q112: lem-trf-normalized-free-module-comparison-calculus

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normalized-free-module-comparison-calculus.json`: statement, now split in seven steps. No exact Mathlib match; no statement changes. Existing metadata and inherited searches retained, with five newly executed logged searches appended.
- `citations.json`: five verbatim statement excerpts, one for every node cited by a proof step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` by the exact blueprint id, normalized/free terminology, semilinearity, and free comparison declarations. The exact tag has no declaration. The freeHomEquiv declarations and their uses found in the project concern constant-index free sheaves or other special settings; they do not state every clause under the item's hypotheses. No sorry declaration was treated as a finished proof.

## WANTED

None. The cited Stacks source and current blueprint are available locally.

## What was wrong or incomplete

The item was unsplit, with no proof or proof dependencies. Its statement is correct as a conditional assertion; its representing properties are hypotheses, not consequences to establish here. The Stacks proof (08TQ) uses the three free-module identifications for differentials but does not explicitly state this generalized conditional calculus. Accordingly the proof is marked agent-written, elaborating the generator-extension construction in 04BL and the comparisons in 08TQ. The source metadata is retained.

The critical type issue is that coefficient-changing maps are semilinear. Injectivity for linear maps cannot be applied to them until their common target is regarded as a module by restriction along the coefficient map. Step 1 constructs this scalar action explicitly; step 3 applies the assumed representing property to that actual target. Step 2 checks that applying the finite-limit-preserving functor preserves the semilinear operation equation.

The unit and chapter records were read. This item is an auxiliary free-module input in the recorded ancestry of the differential comparison, not the key statement of sk-i-curve-zero; no unit record is changed. Neither the unit route nor any target is changed. The existing free-sheaf universal-property node, rather than the geometric-inverse-image parent, supplies the reusable theorem. The parent is not cited, avoiding a cycle.

## What could not be finished

Nothing in the one-level split remains unfinished. Its existing universal-property dependency is used through its statement; this delivery does not claim to prove that dependency.

## Not duplicates

No new nodes were created. The entire DAG and blueprint were searched for free-module, free-sheaf, normalized-comparison and semilinear terminology, and the DAG's sources were checked for 04BL and 08TQ. `lem-trf-free-module-sheaf-universal-property` already gives the universal property needed in steps 1 and 6. `lem-trf-geometric-free-module-hom-equivalence` establishes the representing hypothesis in the geometric-morphism case; that hypothesis is already assumed here. `lem-trf-geometric-inverse-image-free-module` is this item's parent, depends on the item, and is not a usable proof dependency. No duplicate comparison or clause node was introduced. Whole-blueprint searches for free module, free sheaf, normalized and semilinear found no blueprint node stating this item in another form; `same_as` remains empty.

## Mathlib searches

The sandbox initially contained only dispatcher marker files, without an item copy, report or prior search log. The live item was therefore the starting copy. Its inherited searches were retained. The new searches were run with the required msearch.py command and recorded in `searches.jsonl`: one Loogle query, one grep query, one LeanSearch query, and two different LeanFinder phrasings. Every service answered and every set of hits was read.

Read Mathlib's `Algebra/Category/ModuleCat/Sheaf/Free.lean` lines 39-77, 99-111 and 180-230; `Presheaf/Free.lean` lines 51-108; and `Sheaf/PullbackFree.lean` lines 20-115. `SheafOfModules.freeHomEquiv_freeMap` and `mapFreeIso` work with a constant index type, whereas E here is an arbitrary sheaf. `PresheafOfModules.free` allows presheaf generators but works over fixed coefficients and does not itself state the sheaf comparison and its coherence. `SheafOfModules.pullbackObjFreeIso_hom_naturality` assumes the pullback/adjunction setting and constant generator types. None is an exact or one-line match for the complete conditional item. These are genuine partial results, not claimed leaves.

## Review by Q112

I read Stacks `sites-modules.tex`, Tag 04BL (`lemma-universal-module`), especially its construction of O_2[F] as sheafification and its sectionwise extension rule, and Tag 08TQ (`lemma-pullback-differentials`) and its proof giving the three free-module comparisons. I verified the tags against `stacks-project/tags/tags`. I also read the current main-20261015 blueprint's locality statement and smooth-curve unit, and the DAG chapter/unit records. There is no new-node source to audit and no SGA source is used.

For step 1 I opened the statements of `def-weil-sheaf-of-modules-category`, `lem-trf-free-module-sheaf-universal-property`, and `def-weil-presheaf-modules-sheafification`. They give respectively the sectionwise linearity convention, the actual Hom bijection for arbitrary sheaf generators, and unique factorization through module sheafification. The free-sheaf node explicitly applies to every B-module sheaf M; N restricted along b is such a module by the action and restriction equations written in the step. Its generator-extension description really gives the displayed finite-sum formula. This is not an inference from a definition of a free module alone. No injectivity, surjectivity or flatness of b is needed.

For step 2 I opened `def-weil-pbc-algebraic-inverse-image`. Its statement explicitly describes transport of scalar multiplication and addition along finite-product comparisons. Applying the functor to the semilinear operation diagram and using naturality of the comparison gives precisely the claimed semilinearity; the step writes this equality. We do not assume an adjunction, preservation of arbitrary colimits, or that all functors between module categories preserve free objects.

Step 3 uses the semilinearity established in step 2 and the scalar-restriction construction from step 1. Both maps have exactly the same coefficient map Lb, the same source L(B[E]), and the same target (LB')[LE'] restricted to LB. The two displayed generator calculations have identical endpoint i_(LB',LE') composed with Lu. The needed injectivity is the representing bijection in this item's own hypotheses, not an uncited theorem. Step 4 is the direct composition of the normalization and the generator equation from step 1, valid for an arbitrary v. No additional node is used by either step.

For step 5 I checked the actual projection square, rather than asserting product compatibility without its maps: q_i lambda = L pi_i, and the two maps from L(B[E]) to (LB)[LE_i] have the same generator restriction. The representing injectivity applies over LB. For I empty, finite-limit preservation supplies L1 isomorphic to 1, the generator equation remains meaningful, and the projection clause is vacuous. I specifically checked that the argument never treats the free module on the terminal sheaf as zero. A singleton family reduces to the same generator calculation.

For step 6 I reopened the free-sheaf universal-property statement and checked that its injectivity applies to the two B-linear endomorphisms p^id and id of the identical constructed B[E]. Normalization supplies precisely the required equality on generators. For step 7, step 2 makes K(p^L) linear over KLB; the composite operations and identifications required in the item's hypotheses make its target the source of p^K. The displayed calculation of r composed with KLi uses each normalization once. The representing property for KL, explicitly assumed in the statement, supplies injectivity. There is no assertion of an adjoint to K or L and no hidden use of the geometric-morphism Hom-equivalence node.

Against delivery-errors B-E, I checked that the statement introduces all its objects and retains its definition dependencies; all cited files were read and every excerpt in citations.json is a verbatim substring of the relevant statement. Every proof dependency is in a step's uses, and conversely. The genuinely reusable non-elementary input is the already existing free-sheaf universal property; scalar restriction and transport are explicit operation checks, and the remaining equalities are short applications of the assumed injective restrictions. I did not create elementary nodes, duplicates, or new nodes restating clauses. Each proof step is shorter than 2000 characters. The source does not prove this generalized assertion verbatim, so the proof origin is candidly agent-written.

I checked the empty generator sheaf (uniqueness into every module, with no chosen generator needed), empty product, zero ring sheaf, noninjective and nonsurjective coefficient maps, arbitrary noninvertible v, identity functor, and K or L equal to the identity. All the equations remain well typed and the same uniqueness argument applies. None requires a basis of global sections or objectwise generation after sheafification. The sites are small as required by the existing universal-property node; no large indexing category or derived identification appears. No statement correction or STATEMENT-DISPUTED entry is needed.
