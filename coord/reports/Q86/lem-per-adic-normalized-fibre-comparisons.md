# Q86 stage-1 report: lem-per-adic-normalized-fibre-comparisons

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-normalized-fibre-comparisons.json`: statement, now split into twelve proof steps; not a Mathlib leaf. Its statement, statement dependencies, creation record and blueprint provenance are preserved.
- No new nodes and no new Mathlib leaves. Twenty existing nodes supply the proof dependencies. The existing field-scalar-exactness and constructible-subset Mathlib leaves are reused, not newly delivered.
- `citations.json`: one verbatim contiguous statement excerpt for each of the 43 step/node citations.
- This report. Sandbox-only working files contain the writing scripts, source extracts and actual search log; they are not DAG deliveries.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the blueprint tag and normalized fibre terminology, and inspected the concept search hits. The normalization matches in ProperNormalizedFibres concern Stein idempotents; the lisse-rank and adic-pullback hits do not state this item's complete comparison/descent/rank assertion. I found no project declaration that supports an ATTACH. No Lean was written or compiled.

## WANTED

None for this split. The main source and all additional sources read are already in the repository. No new source is requested.

## Corrections and scope

The item had no proof. Its statement is retained: I found no statement dispute. The current main-20261015 ancestor file retains the smooth perverse-pullback statement but has no proof; the older master file has the first-paragraph ordinary-exactness/support argument identified by the item's existing `blueprint.from.place`. This split makes that ordinary-fibre input precise. It neither proves smooth purity nor changes the perverse unit's argument or its dependencies.

I have not used the parent `lem-per-adic-heart-pullback-fibres` as a proof dependency: it depends on this item. The finite-stage exactness and pullback t-exactness inputs are the separate existing sibling nodes specifically allocated for them. Existing unsplit dependencies are used as statements, not represented as already proved.

The scalar-limit step does not interchange tensor with an arbitrary inverse limit. It reconstructs a finite free module after the finite ring extension, reducing its completion to the existing finite-module adic theorem. The rank step explicitly identifies the continuous coefficient ring with the pulled condensed coefficient ring before using the existing rank-locus theorem. The common-stage exactness step explains why a short exact heart sequence can be represented by one at a finite enlargement; finite-diagram descent alone would not justify that assertion.

## Searches and existing nodes

I ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `pullback stalk`, `normalized fibre`, `scalar fibre`, and `lisse rank`, together with searches through all DAG nodes and the Lean source. The rank search points toward other lisse results but no blueprint node states this complete normalized comparison assertion. The generic rank theorem `det-lem-stratified-lattice-rank` already exists and is reused.

All five current Mathlib searches were made with the required `msearch.py Q86 lem-per-adic-normalized-fibre-comparisons` command and read. The log has the exact query/tool pairs. LeanFinder returned generic condensed locally constant functors, finite profinite factorization, and free-sheaf pullback naturality. Loogle returned no hits. The first source grep returned three IsScalarTower lines, unrelated to adic fibres; the second grep returned no hits. LeanSearch, with a different phrasing, returned topological finite-fibre and condensed-discrete functors and intermediate-field rank formulas. None states this constructible adic assertion or specializes to it in one line. All services responded; no unavailable search is disguised as a negative result. The inherited Q119 records remain, separately from these current Q86 entries.

## Not duplicates

No new node pairs: this delivery creates no node. All intermediate facts that already have nodes are cited. The pure-tensor, inverse-limit projection, basis and locally-closed-refinement calculations are written as proof steps rather than packaged as new nodes or renamed clauses of this item.

## Review by Q86

I read Bhatt–Scholze, Section 6.8, especially Definitions 6.8.3 and 6.8.6, Proposition 6.8.4, Proposition 6.8.14 and Remark 6.8.15, directly from the local PDF. Proposition 6.8.4 supplies the normalized lattice-system context and local existence of lattices; it does not itself state the entire result under review. The proof is therefore marked as written by an agent. I also read Deligne Weil II (1.1.1), printed pp. 146–147, for compatible finite quotient systems, rational morphisms, finite extension and the coefficient 2-colimit. I read Stacks `etale-cohomology.tex`, Tag 03Q1, `lemma-stalk-pullback`, including the germ computation; `algebra.tex`, Tag 09B8, `lemma-limit-complete`, for the reconstruction used in step 4; and the rank node's main-20261015 blueprint statement. For the common-stage exactness argument I checked BBD 1.3.3–1.3.6 in the local PDF against the existing heart cone/kernel statement. There are no new nodes needing separate source audits.

1. Step 1 uses the actual statement of `lem-per-continuous-rational-derived-realization`: it identifies the localized heart with continuous constructible module sheaves. `lem-per-adic-normalized-fibre-exactness` supplies the lattice-limit fibre and fractional-map prescription, and `lem-per-lisse-completed-system-comparison` supplies reconstruction from finite-free normalized systems. The schemes and coefficient fields have precisely the hypotheses of these nodes. I do not infer any statement about unrestricted pro-etale stalks or require a global lattice.

2. Step 2 uses the germ-normalized isomorphism in `lem-weil-pbc-inverse-image-stalk-germ`, not just an abstract equivalence of fibre functors. That formula proves the identity and composition equations on generators. `lem-pod-etale-stalk-tensor-scalar` explicitly has the scalar extension formula for arbitrary ring homomorphisms, so quotient reductions need no flatness assumption. Naturality in coefficient multiplication proves linearity of the abelian stalk isomorphism. The mixed finite-level square is checked on the stated pure tensors.

3. Step 3 uses the lisse-system comparison's explicit compatibility with module pullback, the realization theorem's comparison with the actual completed rational pullback, and `lem-per-adic-stratified-pullback-texact`'s local balanced finite-free degree-zero model. These statements identify the functor being computed; merely quoting a stalk isomorphism would not do so. The normalized fibre node supplies the action on a divided integral map, so naturality is checked with the same denominator on both sides. No flatness of the coefficient structural map is used.

4. Step 4 uses clause 3 of `def-pod-lisse-l-adic-sheaves` for the actual ramified scalar system with index ceiling(m/e). The finite scalar stalk theorem identifies each term, while `lem-pod-adic-limit-finite-modules` gives both M modulo powers and completion of finite modules over the target DVR. The finite-free fibre from the normalization node remains finite free after tensor with the target integers. The lisse-system comparison connects this calculation to integral scalar extension. Thus the map is the quotient-induced comparison, not an untracked isomorphism of vector spaces. Both uniformizers disappear into the same module tensored with L.

5. Step 5 uses the stated normalized scalar associators in `prop-weil-pbc-scalar-extension` and the scheme/scalar compatibilities of the lisse-system comparison. The germ and finite scalar stalk nodes provide the generator formulas. I wrote both routes through the mixed square and through a tower of fields as s tensor a tensor b mapping to s tensor ab. Passing these equalities through quotient projections and inverse limit proves the required equations without silently changing associators.

6. Step 6 uses the raw rational realization's full faithfulness from the lisse-system comparison and the normalization node's natural change-of-chart and fractional-representative comparisons. These statements allow a change of lattice to be represented by a divided integral map. Naturality from steps 2–5 gives the overlap equation; a representative difference killed by a uniformizer power induces the zero rational map. This is why the construction is independent of charts and denominators.

7. Step 7 uses the exact morphism representative and transport relation of `def-weil-pbc-finite-stage-pair-category`, together with the representative-independence and finite-diagram property of `prop-weil-pbc-common-stage-calculus`. The sibling `lem-per-adic-common-stage-truncations` explicitly identifies the common heart as the isomorphism closure of finite-stage heart pairs. The conjugated formula for a representative is stated in the step, and step 5 supplies invariance under the scalar associators.

8. Step 8 uses clause 3 of `lem-weil-heart-short-exact-triangles` for kernels and cokernels as cohomology of cones, the definition of common-stage cones, and the common-stage truncation comparisons. Those are exactly the tools needed to represent homology obstructions. Common-stage calculus then kills their identity maps at some finite enlargement when their classes are zero. This establishes finite-stage exactness before applying the normalized exact fibre functor and the existing `lem-weil-field-scalar-extension-exact`. I corrected the tempting but insufficient argument that finite-diagram representability by itself descends short exactness.

9. Step 9 uses the normalization node's explicit detection of zero objects, isomorphisms, zero maps and short exactness. Common-stage calculus supplies a stage where a short-complex equation holds. Field extension is exact by the scalar-exactness leaf. I wrote the elementary faithful-scalar argument with bases; it applies even when the overfield is the infinite algebraic closure, and it does not rely on a finite extension degree. The kernel/cokernel argument then proves conservativity.

10. Step 10 uses the sibling pullback node's actual common-stage pullback and common-stage calculus. The mixed square proved earlier is what makes the descended fibre comparison independent of the chosen field and natural for representatives. I do not replace this with a choice of unspecified comparison isomorphisms.

11. Step 11 uses the realization theorem for the finite lisse stratification, `lem-weil-pbc-continuous-coefficient-realizations` for the precise coefficient-ring identification, and `det-lem-stratified-lattice-rank` for clopen, finite-range ranks. It uses the normalized lisse-system equivalence and fibre prescription to identify this rank with dimension. The constant-stalk clause of `lem-pod-lisse-tensor-and-scalar-extension` is the finite-level rank calculation, rather than an unjustified stalk/limit interchange. Each stratum is noetherian and quasi-compact under the finite-type hypotheses. Equal finite dimensions give isomorphic fibres over a fixed point by choosing bases; I make no false assertion of a canonical path between geometric points.

12. Step 12 uses the definition of finite locally closed stratification, the noetherian finite-union-of-locally-closed clause in `def-weil-constructible-subset`, and the common-stage heart representative theorem. Clopen refinement within a locally closed stratum is locally closed in X. The basis calculation proves preservation of rank under every field extension, including the algebraic closure; positive rank is equivalent to a nonzero finite-dimensional fibre. This step is marked elementary because it is precisely that finite refinement and basis calculation from the preceding results and cited definitions.

For the B–E checklist, I checked that every proof use has a verbatim quote of its actual statement in `citations.json`, and that no cited definition is used as a substitute for an unstated theorem. Off-unit statements are declared as generic tools in `split_report.tool_uses`; they supply stalk, coefficient, rank, field and heart calculus and do not replace the unit's perverse argument. No new node is a duplicate, elementary fact or renamed item clause, since none is created. The statement introduces its objects and keeps every original hypothesis. I checked the small cases: empty schemes/strata contribute no points; rank-zero lattices give zero fibres and empty positive-rank loci; identity coefficient extension and identity pullback give identity maps; ramified extension uses the correct quotient index; arbitrary non-flat g uses the cited stratified finite-free model; disconnected strata allow varying finite rank. The family of fibres on the empty heart is vacuously conservative since the normalization input detects the sole zero object. No argument assumes smoothness, an algebraically closed base field, connectedness, or globally constant rank.

I also traversed statement and proof dependency edges of the reused comparison, rank and normalization inputs to this item: none reaches it. Every proof step has length below 2000 characters, so there is no long inline sublemma requiring a new node under the long-step rule. The server's preliminary `review_split` returned PASS with zero new nodes. I did not run any of the three prohibited check scripts on this machine.

## Unfinished work

None within the authorized one-level split. Existing unsplit dependency statements remain their owners' items, and are not claimed proved by this delivery. Final server dry-run and delivery results are recorded below when available.
