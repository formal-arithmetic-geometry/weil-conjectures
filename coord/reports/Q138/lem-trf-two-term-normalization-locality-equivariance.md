# Q138: lem-trf-two-term-normalization-locality-equivariance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-two-term-normalization-locality-equivariance.json`: statement, split into eight argument steps, no Mathlib match for the whole statement.
- `citations.json`: one literal statement excerpt per cited node per step.
- `searches.jsonl`: real msearch results, retained without alteration.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not a library or launcher change.

New nodes: 0. Mathlib leaves created: 0. The item statement and statement dependencies are unchanged. All blueprint provenance and imported fields are retained; `same_as` remains empty after whole-blueprint searches.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact id, kernel normalization, and determinant/localization terminology. The scalar characteristic-polynomial and Koszul-comparison declarations found do not give this item's maps or all its clauses. No complete project proof was claimed.

## WANTED

None. All mathematics used is in the checked-in Stacks sources and existing nodes. The inherited brief mentions `coord/dag-sync.md`, absent from this clone; the current direct-delivery instructions supply the relevant paths and restrictions.

## Findings and corrections

The imported item has a mathematically sound statement but no proof. Its source points to 0FJC, whose proof is omitted, and the first and final paragraphs of 0FJK. I supplied the missing arguments rather than creating nodes restating the item's clauses. There is no statement dispute and no change of route. The current blueprint ancestor `lem-trf-local-term-locality` and the current unit are read as the provenance of the existing semistable/adjunction branch; this small algebra lemma does not replace their geometric argument.

The split needs neither an arbitrary-flat-base-change theorem nor a Hom-localization theorem as an extra black box. Kernel localization is checked with fractions. Dual localization is constructed by a finite dual frame and its inverse is verified by evaluation. The arbitrary-module equality assertion is proved using the existing basic-open/unit-ideal criterion, rather than citing the ring-only jointly-injective node (which would be an invalid C4 citation for general modules). No source proof is used as though it were the statement of a cited node.

Mathlib searches ran through the prescribed msearch command: LeanFinder twice (different phrasings), LeanSearch, Loogle, and two source-grep patterns. The results were read, including ExteriorPower/Basic.lean map_apply_ιMulti, map_comp, and oneEquiv_naturality. These supply elementary pure-wedge operations, not the two-term determinant-line normalization statement. Projective-resolution naturality has different objects; det_conj/det_map are scalar endomorphism determinants; the StandardEtale hit is unrelated. The existing five searches of Q30 are preserved, and the actual six current search records are appended with their exact queries, results summaries and digests. No new node requires a fresh search record.

## Review by Q138

I read Stacks `more-algebra.tex`, Tags 0FJA (socle and determinant charts), 0FJB (both exact-sequence determinant constructions), 0FJC (isomorphism naturality), 0FJI (two-term determinant and the kernel generator), and 0FJK (the first diagram and the final reduction to local rings). I checked their tags in `tags/tags`. I also read `algebra.tex` Tag 00HN, especially its annihilator proof of elementwise detection, and read the existing nodes for the basic-open criterion and finite projective free cover. The current blueprint node and unit were read from `literature/blueprint/latest/` and the unit/chapter records. This is an agent expansion of the Stacks arguments: the source omits the naturality proof and does not present our explicit dual-frame argument.

Step 1 uses the fraction zero criterion stated verbatim by `def-weil-pbc-module-localization` and clause (i) of `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`. For each value of the difference of two maps I form its annihilator; each prime misses an annihilating denominator, so the annihilator generates the unit ideal. This establishes equality for arbitrary target modules, with no projectivity assumption. Both cited statements have exactly these hypotheses and conclusions.

Step 2 uses `lem-trf-two-term-kernel-normalization` for split exact sequences, finite projective kernels and invertible kernel differential, not for the locality claim being proved. The fraction definition gives the kernel comparison explicitly: a kernel fraction has numerator killed into the kernel by an extra denominator. The finite standard free cover node states the existence of a cover for direct summands of finite free modules; localizing at a prime in one of those opens gives a free basis for every term. This is the correct finite-projective hypothesis for all three modules. I checked that no cited determinant/chart node depends on the item.

Step 3 uses only the already supplied split sequences and inverse kernel differential from the kernel-normalization node. Its lifting and correction argument checks both cohomology degrees explicitly, so the notation for the localized normalized map is justified without an unquoted exactness or quasi-isomorphism-preservation theorem. It never assumes either differential of P or Q is injective.

Step 4 uses the exact statement of `lem-trf-projective-determinant-chart-descent`: canonical top-exterior-power charts commute with every further localization. The tensor node gives bilinearity and generation by pure tensors, and the localization node gives fraction equality. The finite-projective determinant-line assertion comes from `lem-trf-projective-determinant-exact-sequence`. A finite free retraction supplies a dual frame, and I wrote the two inverse maps for localized duals; evaluation checks both inverse equations. Thus no extra non-elementary dual base-change fact is hidden in 'canonical identification'.

Step 5 uses the explicit further-localization clause of the exact-sequence determinant node and the definitions and unique inverse from the kernel-normalization node. I checked that its kernel identification is the one of Step 2, and the displayed generator is the determinant of the actual restricted differential, not an independently chosen trivialization. Preservation of the inverse follows from its two inverse equations. This is a short assembly from the stated maps and the preceding explicit comparisons.

Step 6 uses the kernel-normalization node to ensure that both kernels are finite projective, and the exact-sequence determinant node for its ordered-wedge formula. The square au=va' gives a genuine restriction of u and its inverse; transported quotient basis vectors have lifts u(p'_k). Both sides send the generator to the identical kernel-first wedge. This proves the naturality clause directly; I did not invent a new node for that same clause. Step 1 supplies the global equality detection. The degree -1 superscript is distinguished from inversion of a linear map in the chain equation.

Step 7 uses the kernel-normalization node's Hom interpretation and its precise ordinary-symmetry definition of Gamma, and the tensor-product node's pure-tensor characterization. Evaluating D(c) on Hom gives conjugation by det(c^0) and the inverse of det(c^{-1}), which takes det(d_N') to det(d_N) by the chain equation. I checked the inverse-dual direction separately: from UG'=G(C tensor V), taking inverse duals gives (U^{-1})^vee(G'^{-1})^vee=(G^{-1})^vee((C^{-1})^vee tensor (V^{-1})^vee). Tensoring the degree-zero equality then gives the required Gamma square with ordinary symmetry and no graded sign.

Step 8 uses exactly the two inverse equations for T supplied by the kernel-normalization statement. Substitution of the generator equality into the Gamma square gives D(u)F_a'=F_a D(v); multiplication by the inverses gives T_a D(u)=D(v)T_a'. This checks the domains as well as the order of composition.

I reviewed delivery-errors B through E against the actual files. There are no new-node shape or duplicate issues, no tag-only proof dependencies, no use of the source's proof as a cited node's statement, no new clause disguised as a split, and no argument relying on a missing finiteness/Noetherian/constant-rank assumption. Every non-elementary construction used is in an existing cited statement; the fraction, dual-frame, wedge-generator and cancellation arguments are written out. All steps are below 1300 characters, so none meets the long-step threshold.

Edge cases checked: R=0 (all modules vanish, the prime-family comparison is vacuous but valid); the identity map (kernel rank zero and normalization is the identity); Q=0 (the kernel is P and its invertible differential gives the generator); degree -1 or degree zero rank zero; ranks varying between components (all basis calculations are chartwise); characteristic two (no division by a sign or 2); and non-injective differentials of P and Q (only the acyclic kernel differential is inverted). For rank-one kernel differentials d,d' and component maps c^{-1}=r,c^0=s, the chain equation sd'=dr makes D(c) act by s/r and sends the generator d' to d, checking the dual direction in a scalar example.

## Not duplicates

No new nodes were created. Searched the whole DAG for 0FJC/0FJI/0FJK and localization/determinant notions, and the whole imported blueprint with `blueprint_refs.py search determinant`, `determinant localization`, and `kernel normalization`. The existing exact-sequence and chart-descent statements are cited, not recreated. The ring-only local-injectivity node is deliberately not used for general modules.

## Unfinished work

No mathematical portion of the item is left to split. Stage 2 and all Lean writing/building remain outside this task. Required server validation and direct delivery are performed after this report.
