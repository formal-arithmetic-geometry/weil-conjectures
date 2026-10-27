# Stage-1 report: lem-sfb-augmented-scalar-roos-resolution

## Files written

`dag/nodes/sec-six-functors-basics/lem-sfb-augmented-scalar-roos-resolution.json`: existing statement node, now split into nine steps; no new nodes and no Mathlib leaves. The mathematical statement and its existing statement dependencies are unchanged. The proof, proof dependencies, proof origin, split report, blueprint place and recorded searches have been filled. `citations.json` contains a verbatim passage from every cited node for every proof-step citation. `searches.jsonl` records the actual five searches run for this item; the existing earlier search records in the item are retained.

## Attachments

None. The exact item tag has no declaration under `lean/WeilConjectures/`. Searches for Roos and scalar restriction find generic project declarations, including `CategoryTheory.roosComplex_quasiIso` in `Algebra/Homology/RoosComplex.lean` and `CategoryTheory.roos_comparison_maps` in `Algebra/Homology/RoosComparisonMaps.lean`; they state individual components, rather than every clause of the item. They are therefore not attachments. The corresponding existing DAG theorems are reused, rather than recreated.

## WANTED

None. Sources required for this split are present.

## Findings and changes

The imported item had a complete statement and no proof. The whole-DAG and blueprint searches found the existing normalized strict-Roos theorem, its arbitrary-K-injective-resolution comparison, and exact pro-etale products. Those are sufficient; extracting new nodes for individual cone-coordinate calculations would create elementary or duplicate nodes. The proof is marked `proof_origin.by = agent`: the blueprint final paragraph suggests exact restriction plus products, while the written coordinate and resolution-unit equations are the worker's refinement. Stacks 0941 proves the K-injective Roos computation (choosing injective terms), 07KC proves the exact-product derived computation, and the already-existing arbitrary-resolution DAG theorem supplies its stronger arbitrary-K-injective zigzag. The proof does not attribute that stronger statement directly to 0941.

No statement dispute, unit-route error, omitted hypothesis, or unavailable source was found. No Lean file was written or compiled. No compiler, Lake, global build, local preflight, local check_dag or local review_split was run. All writes are within this sandbox. The unit/chapter records are read unchanged: this is an auxiliary node of the inverse-image comparison, not the unit key node.

## Search results

I searched the entire DAG and the blueprint index for Roos, K-injective and restriction-of-scalars statements, and read the candidate statements. The Mathlib searches executed through msearch.py were:

- LeanFinder: `Restriction of scalars for sheaves of modules preserves products and the augmented Roos complex computes the total derived inverse limit naturally including its unit`.
- Loogle: `CochainComplex.mappingCone`.
- grep: `[Rr]oos|restrictScalars.*[Ll]imit|[Ll]imit.*restrictScalars`.
- LeanSearch: `The augmented mapping fiber of one minus shift on an inverse sequence of unbounded sheaf complexes represents derived inverse limit and its adjunction unit`.
- LeanFinder, second phrasing: `Natural comparison between a Roos mapping cone and inverse limit of a K injective resolution, compatible with scalar restriction and chain homotopies`.

All services returned results. I read the mapping-cone source and ModuleCat change-of-rings declarations, including `preservesLimit_restrictScalars` at ChangeOfRings.lean:932 and `restrictScalars_map_exact` at ChangeOfRingsExact.lean:36. They are generic components, not a one-line specialization proving the item, which includes unbounded ring-sheaf towers, actual derived units, and cross-ring augmentation normalization. No absence is inferred from a failed service. The recorded tool/query strings are copied from searches.jsonl without inventing searches.

## Not duplicates

No new nodes are created. Existing candidates differ as follows, which explains why the item is split using them rather than attached to or replaced by one of them.

lem-sfb-augmented-scalar-roos-resolution vs lem-weil-strict-roos-comparison: the latter is the one-ring normalized Roos functor and augmentation theorem; this item adds the scalar restriction comparison, diagonal chain/homotopy formulas, and cross-ring augmented equation.

lem-sfb-augmented-scalar-roos-resolution vs lem-sf-strict-roos-derived-limit-comparison: the latter gives the arbitrary-K-injective zigzag and evaluations, but no ring change or cross-ring canonical-unit equation.

lem-sfb-augmented-scalar-roos-resolution vs lem-weil-pbc-exact-products-roos-comparison: the latter gives a generic derived-functor comparison, but does not give the scalar map or all the strict-coordinate and homotopy clauses here.

lem-sfb-augmented-scalar-roos-resolution vs lem-cbc-exact-functor-rlim: that triangulated theorem explicitly supplies no unique canonical comparison from bare triangle data. Here the chain-level tuple identity fixes the comparison and its augmentation behavior. I do not use the bare triangle existence theorem to infer a canonical unit equation.

## Review by Q61

I read AGENTS.md, the worker brief, the stage-1 rules, SETUP.md's three blueprint levels, GOAL.md, the chapter and unit records, and both copies of delivery-errors B–E. I read the first and final paragraphs of the current `det-lem-int-tensor-pullback.proof.md`, Stacks sites-cohomology.tex around lemma-derived-limit-is-ok (Tag 0941), derived.tex around lemma-products (07KC) and lemma-K-injective (070I). For the product input I read Bhatt–Scholze Propositions 3.1.9, 3.2.3(1) and 4.2.8 in the local PDF, extracted into the sandbox. There are no new-node sources to review. Every dependency statement was opened and the precise passages used were copied into citations.json.

Step 1 uses def-pc-sheaf-restrict-scalars for the unchanged underlying abelian sheaf and maps, def-weil-sheaf-of-modules-category for sectionwise kernels and sheafified cokernels, and lem-weil-proetale-countable-products-exact for sectionwise exact countable products for an arbitrary commutative ring sheaf. The hypothesis is exactly the small pro-etale site of a scheme, for R as well as C; I did not replace this by an exact-products theorem for ordinary modules. Scalar restriction is exact because kernels and cokernels retain their underlying abelian sheaves, and its product map and inverse are identity maps on sections. Finite biproduct preservation then follows by coordinates.

Step 2 uses the abstract-derived-category definition for the actual shift/cone signs and the inverse-system and transition-endomorphism definitions for the strictly commuting square. I wrote D²=0 and the projected equation F'f^Pi=f^Pi F; those two equations prove the chain map and its diagonal inverse. The same calculation proves the chain isomorphism c_W itself. Step 3 uses the homotopy formula of def-pur-kinjective-complex and the localization-through-homotopy convention of def-weil-abstract-derived-category. Expanding D'K+KD gives positive diagonal f-g in both coordinates; the potentially troublesome mixed term is HF-F'H and vanishes by transition compatibility. This corrects a possible implicit sign shortcut rather than hiding a cone lemma.

Step 4 uses the inverse-system and transition-endomorphism definitions; F b^Pi=0 proves the augmentation is a chain map and the two augmentation composites are literally the same tuple with zero first coordinate. These three coordinate steps are elementary and do not quote an uncited standard comparison theorem.

Step 5 uses lem-weil-strict-roos-comparison for a natural normalized rho, lem-sf-strict-roos-derived-limit-comparison for both quasi-isomorphisms for EVERY K-injective tower resolution, the ringed strict-tower homotopy-limit theorem for the actual total right derived inverse limit, and def-sfb-right-derived-functor for the universal unit eta and its invertibility on K-injectives. Countable products are exact for both rings by Step 1. The small model is chosen in the module universe. I specifically checked that the auxiliary comparison statement allows a K-injective I without injective terms; using only the injective-terms clause of the other Roos theorem would not suffice. The augmentation of I and naturality on q identify the zigzag normalization with rho, with the target transported by Rlim(Qq) inverse.

Step 6 uses the universal natural transformation stated in def-sfb-right-derived-functor and the canonical augmentation clause of lem-weil-strict-roos-comparison. I wrote the equation R(q) alpha=j_I lambda and canceled Qj_I to get rho Qalpha=d_I Qlambda. Then naturality of eta at q and b identifies this with Rlim(Qb) eta_DeltaL. This explicitly checks the actual constant-tower unit instead of inferring equality of maps from an isomorphism of objects. Step 7 uses only the supplied comparison homotopy, its degree formula, localization, and the same naturality of eta. The compatible tuple homotopy lands in ker F and hence in lim I; it proves equality even when ap and qb are merely homotopic. No preservation of K-injectives by scalar restriction is asserted or used.

Step 8 uses the Mathlib-leaf exact-functor-derived-factorization statement to define D(r) with its natural localization comparison, and the naturality assertion of the strict Roos theorem. The displayed conjugation formula fixes beta; substituting it into the chain-level naturality square gives naturality of beta. Step 9 uses those same cited statements and the already-proved chain augmentation equation to compute the image of the canonical map. No uniqueness of a morphism of triangulated Roos triangles is assumed. The two equations show exactly what compatibility and conjugation mean.

I checked edge cases: the zero complex/tower gives all zero maps; identity transitions give F=1-shift and diagonal constant augmentations; zero transitions force a strict augmentation to be zero and make the fiber of F=id contractible; inverse isomorphisms and identity ring maps reduce to the stated identities. The formulas work in every integer degree and in the empty scheme/zero module category. For an arbitrary ring map (including a nonflat quotient), the proof uses exact restriction only and never assumes that restriction preserves injectives. No source uses SGA. There are no long non-elementary steps (all nine are under 1,200 characters), no unsplit clause hidden as a new node, and proof_deps equals the union of uses.

The four off-unit tools are declared under split_report.tool_uses for maintainer review: exact pro-etale countable products, normalized strict Roos comparison, arbitrary-K-injective Roos comparison, and the ringed strict-tower total derived limit. These are generic tools implementing the blueprint final paragraph's given route, not replacements for a unit step. No maintainer-owned tool_uses field was written.

## Unfinished work

None in the one-level split. The required dry run and delivery results are recorded below after execution. Any unresolved global DAG work is outside this item's scope.
