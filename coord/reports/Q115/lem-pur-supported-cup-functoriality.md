# Repair of lem-pur-supported-cup-functoriality

## Files written

The item retains its statement and stmt_deps byte-for-byte against the current repository. Its five-step assembly has 2351 characters. Four new statement-only nodes remain, all status unsplit, with empty proof/proof_deps and null proof_origin; none is a Mathlib leaf.

- lem-pur-signed-twist-site-transport: mixed-sign multiplication and negative evaluation/pullback extension of the existing root and nonnegative Tate comparison; no Mathlib match.
- lem-pur-closed-source-site-tensor-comparison: section formula for the existing exchange and its site/geometric multiplication equations; no Mathlib match.
- lem-pur-supported-source-system-cup-calculus: label-indexed source/target multiplication assembly using the existing B and t calculus; no Mathlib match.
- lem-pur-unit-kummer-two-site-normalization: degree-one unit-boundary coefficient and two-site normalization; no Mathlib match.

Deleted from this delivery: lem-pur-supported-localization-triangle-normalization. Every substantive assertion it made is reused from the existing nodes in Steps 2 and 4 rather than restated in a new task. The initial dry run was allowed to finish (exit 1, same-tag report omissions, nothing pushed) before any new delivery invocation. The earlier returned version, report, citations, search log and results were retained in returned-report.md, returned-nodes.json, prior-proof.json and search-results/. The current report supersedes the earlier report's claim that the five original nodes were independent.

## Attachments

None. The tag/concept search of lean/WeilConjectures/ finds no exact finished declaration. The library's WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality in lean/Sheaf/Paper/SupportedCupFunctoriality.lean:1932 has sorry at line 1935. No Lean was written or compiler/Lake/build run.

## WANTED

None.

## Returned points repaired

1. Closed-source duplication: the new node no longer asserts etale b, etale mu, either-site flatness, either-site mu invertibility, etale associativity/symmetry, or the general b/q exchange and geometric/site square. It explicitly takes the etale data from lem-pur-etale-closed-constant-tensor, the pro-etale maps from def-pur-supported-cup and the already normalized q,b from lem-pur-supported-constant-exchange-normalization. Only the section formula, q-mu equation and pro-etale b-mu equation are conclusions. These input nodes are statement dependencies, not uncited proof folklore.
2. Localization duplication: remove the new localization node entirely. Parent Step 2 cites lem-pur-supported-hom-cocycle-normalization for evaluation and lem-pur-supported-hom-pullback for the actual pullback equation and site square. It cites thm-pur-with-support-exactness for restriction/boundary functoriality. Step 4 cites the existing exchange normalization for exactness/cokernel/counit maps, lem-weil-pbc-exact-functor-ses-triangle-image for the precise connecting arrow, and thm-weil-pbc-site-comparison for full faithfulness. There is no replacement localization task.
3. Twist duplication: the new statement takes c and its root/pullback square from lem-amb-finite-root-site-comparison and q+ for nonnegative powers from lem-amb-finite-tate-site-descent. It also reuses lem-pur-signed-line-derived-base-change for constructing the evaluation-normalized negative map. Its conclusions concern this fixed Tate comparison's mixed-sign multiplication, the negative extension of the geometric square and the frame-class coefficient map. The existing root and positive results are expressly cited both in parent Step 1 and in its stmt_deps.
4. Shift comparison: the source-system statement uses B and t of lem-pur-shifted-tensor-morphism-calculus, now an explicit stmt_dep and parent Step 3 citation. Its old duplicate definition of t, and duplicate assertions about model-level associators and unbounded constraints, were removed. Its new role is the source/target multiplication assembly and normalized b/tau cancellation.

The revised count is four new nodes, meeting the batch-5 minimum four. The assembly is below 3000 characters; no step exceeds 2000. No old argument was lost: original Steps 1, 2+6, 3+5 and 8 are assigned to the remaining tasks and their cited existing inputs; original Steps 4+7 are now assembled from already split nodes. All eight original arguments are retained verbatim at the end, including their precise sources and dependency lists in prior-proof.json. The item remains auxiliary to lem-pur-frame-independence, not a unit key theorem; chapter/unit realizations are untouched. No SGA route is used.

## Review by Q115

I read the repair order, current and returned item statements/proofs, all four new statements, coord/delivery-errors.md B–E (both historical copies), the three SETUP levels, GOAL.md, and the relevant unit/chapter. I compared the current item metadata with the sandbox and retained the live inherited fields. I reread the exact main-20261015 lem-pur-frame-independence proof: Unit multiples needs the degree-one Kummer boundary and localization, Permutations needs the graded sign, Elementary shears needs actual geometric pullback. The imported statement requires all schemes and arbitrary morphisms, so no finite-type-only comparison can replace these inputs.

For sources I reread Stacks proetale.tex lemma-relative-comparison (099V), lemma-compare-cohomology (099W) and lemma-compare-derived (09B1), etale-cohomology.tex lemma-kummer-sequence (03PL), and sites-cohomology.tex lemma-cup-product-associative (0FPL) and lemma-cup-product-commutative (0FPM). The last omits its proof: the refinement remains explicitly agent-formulated. For the signed comparison I checked the root-normalized existing nodes, the projection formula in def-pur-frame-class, the exact evaluation characterization in lem-pur-signed-line-derived-base-change and the positive descent statement, rather than attributing negative powers to the latter. The new source comparison's first displayed identification is exactly the statement of lem-cbc-comparison-pullback-sections; degree-zero comparison is the next existing input, with scalars unchanged. The Kummer source is ordinary abelian-sheaf Kummer exactness, with the coefficient map applied only to roots.

Step 1: I opened the statements of all seven cited nodes (including the separate etale twist pullback input). The root node says c is the same-root isomorphism and gives its sigma/d square; descent covers nonnegative powers; the new signed node adds the negative/mixed diagrams. The etale line theorem states local rank-one freeness; locally tensoring with A is exact, so flatness is elementary. The closed tensor node states flatness, specified multiplication and its associative/symmetric and geometric equations. The exchange node states exactness, cokernel and the actual d normalization and gamma/k square. The new source node now supplies only the remaining three deltas. In particular a definition is not cited as an independent product-law theorem.

Step 2: the cocycle statement explicitly gives theta(f)=(f rho)(1) and its derived roof normalization, not only an abstract Hom isomorphism. The Hom-pullback statement identifies the displayed exact-inverse-image formula with canonical localization pullback on both sites and says its comparisons commute. The support exactness theorem explicitly gives functoriality in the pair and coefficients, so supplies the boundary/restriction clauses. Identities/composition follow by substituting the b and tau equations; for b these are also forced by the epimorphic restriction normalization. For full support P=A and b is the constant-unit map. No new non-elementary assertion is inferred from a node's proof.

Step 3: the shifted-tensor statement supplies the actual B, associator and symmetry equations for all integers, and exact-pullback naturality. The source-system lemma assumes precisely flat sources and associative/symmetric mu and h; Step 1 provides those, with scheme intersections reindexed by their canonical associators. Its extra pre/postcomposition with mu inverse and h produces the product in the parent. It does not restate Kummer, localization, site full faithfulness or schemes. This is the explicitly requested old Steps 3+5 task, retaining its scalar/sign work in the appendix while reusing the earlier split signed calculus.

Step 4: the site comparison theorem really states full faithfulness on D+ for every finite ring and every scheme. Both P and the signed coefficient line are degree-zero sheaves, so qualify, and q and the twist comparison identify their images. The exchange statement gives the exact cokernel sequence on both sites and carries its two arrows to the specified arrows. The Mathlib leaf states the actual triangle isomorphism, including its connecting-arrow sign, not merely preservation of exactness. Hom contravariance and the cocycle normalization from Step 2 identify the localization boundary. The multiplication square and the source-system equation identify the precise cup composite in def-pur-supported-cup. Full faithfulness gives the bijection needed to transport laws to all pro-etale classes, so no conservativity of geometric stalks on pro-etale sheaves is assumed.

Step 5: I checked the unit-Kummer statement and def-pur-frame-class against one another. Both use delta followed by comparison and sigma rho, and theta is the inverse-limit-projection map. The new node uses u in H0(G_m), hence produces H1(mu_m); it is not the line-bundle/Picard H1-to-H2 Kummer map. It requires only mA=0, not A flat over Z/m. Applying this with m=ell^n gives the concrete class even when the coefficient index is not divisible by the ramification index.

I checked the edge cases again on the narrowed statements: r=0 is the unit, r=1 is the reused root/projection map and r=-1 sends the dual basis to its functional dual. Opposite twists give evaluation and mixed twists have no cochain sign because the lines are degree zero. Empty C gives P=0, C=X gives A, disjoint C,D give zero intersection and nilpotent thickenings give the same locally constant restrictions. The q/b equations still apply without quasi-compact complements, reducedness or finiteness of v. For a=b=1 the derived sign is -1 and both associativity exponents agree, also for negative integers. For Kummer u=1, v=id, m=1 and A=0 the claimed classes are respectively zero/unchanged/zero/zero. The annihilation ell^n A=0 follows from ell in (varpi), without a ramification divisibility assumption.

For B/C/D/E checks I verified self-contained objects and every definition dependency, source labels/tags, blueprint ancestry and absence of duplicate result conclusions, no hidden proof in unsplit nodes, no cycling, and exact used hypotheses. I retained earlier search logs/results and read their hits before adding searches only for the narrowed twist and source questions. The new results return module duality/rigid-category and structure-sheaf or algebraic etale facts, not these normalized diagrams; none specializes in one line to the new statements. Actual service failures remain marked unavailable. citations.json was regenerated with a substantive verbatim quotation for each cited node of each step. All seven existing nodes requested in the return are now parent citations, and the relevant new statements cite their existing inputs in stmt_deps.

## Not duplicates

lem-pur-signed-twist-site-transport vs lem-pd-section-derived-representative-square: the existing result identifies a condensed/internal tensor-pullback transformation on K-flat section representatives; the new delta identifies mixed-sign multiplication and negative dual evaluation for the fixed finite ordinary etale/pro-etale root/Tate comparison.

lem-pur-signed-twist-site-transport vs lem-pd-section-oplax-total-comparison: the existing result compares internal and section total oplax maps for condensed coefficients, with explicit scalar formulas; the new delta concerns the finite Tate family, its mixed-sign multiplication, negative geometric/site square and frame-class coefficient map.

lem-pur-closed-source-site-tensor-comparison vs lem-pe-left-module-comparison-vanishing-criterion: existing 'Objectwise derived evaluation detects comparison direct-image vanishing'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs sk-prop-sf-comparison: existing 'Bounded-below cohomology comparison'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pe-comparison-injective-left-modules-acyclic: existing 'Comparison pullbacks of injective left-module sheaves are acyclic for arbitrary rings'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-etale-witness-transport-data: existing 'Etale origin witnesses and natural unit comparison for transported functors'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-sfb-etale-module-affine-bound: existing 'Uniform affine étale cohomology bound for finite coefficient module sheaves'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-sfb-classical-module-affine-evaluation-bound: existing 'Uniform derived evaluation bound for classical finite coefficient module sheaves'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-weil-pbc-fixed-module-bounded-constructible-origin: existing 'Bounded fixed-module complexes with constructible sheaf origins have derived origin'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-weil-pbc-fixed-module-derived-hom-bijection: existing 'Derived comparison Hom bijection with bounded below target'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-cbc-abelian-comparison-injective-acyclicity: existing 'Comparison inverse images of injective abelian sheaves are direct-image acyclic'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-comparison-global-resolution-model: existing 'Resolution model for normalized global site comparison'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-support-site-comparison: existing 'Etale-proetale comparison for supported sections and their exterior products'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-site-comparison-edge-section: existing 'Etale/pro-etale comparison preserves higher-image edge sections'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs def-pur-supported-hom-site-comparison: existing 'Canonical etale to pro-etale comparison on supported signed-twist Hom groups'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-support-comparison-common-injectives: existing 'A common injective resolution for etale/proetale comparison'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-closed-source-site-tensor-comparison vs lem-cbc-abelian-etale-proetale-cohomology-comparison: existing 'Etale–pro-etale cohomology comparison for arbitrary abelian sheaves'; the remaining claim is the sectionwise formula of the already normalized closed exchange and its q-mu/pro-etale b-mu equations, for arbitrary schemes.

lem-pur-unit-kummer-two-site-normalization vs sk-lem-geo-cartier: existing 'The cycle class of a Cartier divisor'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sfb-stable-relative-picard-kummer: existing 'Relative semiabelian Picard object and smooth Kummer comparison'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sfb-unit-binomial-finite-etale: existing 'Finite etale algebra of a root of a unit'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sfb-ramified-cartier-supported-purity: existing 'Ramification multiplicity in the supported Cartier purity comparison'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-per-ordinary-kummer-first-chern: existing 'Ordinary derived Kummer first Chern class'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-per-pure-principal-divisor-kummer-residue: existing 'Localization residues of unit Kummer symbols when divisor purity is given'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-per-strict-local-divisor-low-kummer: existing 'Low-degree Kummer cohomology of a strict-local regular divisor complement'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-asd-ordinary-finite-p1-arrows: existing 'Canonical arrows and normalized data for ordinary finite projective-line duality'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-pur-kummer-line-geometry: existing 'Canonical geometry and maps for the Kummer lines'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-kummer-finite-biproducts: existing 'Integral finite-basis cohomology and Kummer exactness'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-kummer-root-line-computation: existing 'Roots-of-unity computation on the two lines'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-asd-ordinary-supported-kummer-boundary: existing 'Relative supported Cartier Kummer boundary specification'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-asd-ordinary-finite-p1-kummer-class: existing 'Scalar Kummer class of O(1) with finite ordinary etale coefficients'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-asd-ordinary-supported-chern-normalization: existing 'Ordinary Chern realization of a normalized supported class'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-kummer-integral-root-comparison: existing 'Integral basis reduction for the Kummer root sheaf'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-asd-ordinary-finite-p1-data: existing 'Normalized decomposition and adjunction data for ordinary finite projective lines'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-supported-cup-functoriality: existing 'Pullback and symmetry of supported Kummer cup products'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-kummer-finite-free-comparison: existing 'Normalized finite free Kummer cohomology comparison'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs def-asd-ordinary-supported-kummer-system: existing 'Normalized ordinary supported Cartier Kummer map systems'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-asd-ordinary-supported-kummer: existing 'Supported Cartier Kummer map for ordinary etale arbitrary finite coefficients'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-asd-ordinary-finite-p1-adjunction: existing 'Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sc-artin-schreier-polynomial-cover: existing 'Surjective etale polynomial cover solving an Artin-Schreier equation'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sc-artin-schreier-sequence-scheme: existing 'Artin-Schreier short exact sequence for arbitrary schemes'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sc-artin-schreier-scheme-section-data: existing 'Construction of sectionwise Artin-Schreier maps'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-unit-kummer-two-site-normalization vs lem-sc-artin-schreier-scheme-section-exact: existing 'Exactness from specified Artin-Schreier section data'; the new claim normalizes degree-one Kummer classes of units on arbitrary m-invertible schemes with arbitrary finite A; it is not a Cartier or Picard degree-two class or bare Kummer exactness.

lem-pur-supported-source-system-cup-calculus vs lem-pur-shifted-tensor-morphism-calculus: existing 'Signed calculus of shifted derived tensor morphisms on ringed sites'; the remaining claim assembles the existing signed B calculus with label-indexed source and weight-indexed target multiplications, including b/tau cancellation.

lem-pur-supported-source-system-cup-calculus vs lem-pur-supported-cup-functoriality: existing 'Pullback and symmetry of supported Kummer cup products'; the remaining claim assembles the existing signed B calculus with label-indexed source and weight-indexed target multiplications, including b/tau cancellation.

lem-pur-supported-source-system-cup-calculus vs lem-pod-cup-product-graded-commutativity: existing 'Graded commutativity of the rational Poincare cup product'; the remaining claim assembles the existing signed B calculus with label-indexed source and weight-indexed target multiplications, including b/tau cancellation.

lem-pur-signed-twist-site-transport vs lem-pe-constructible-comparison-tensor-test-reflection: existing 'Reflection of a single comparison tensor test'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-common-stage: existing 'Canonical common-stage point tensor and coefficient unit'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-slice-normalized-comparisons: existing 'Existence of normalized slice tensor, Hom and Koszul comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-finite-open-tensor-operations: existing 'Canonical finite open tensor and pullback operations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-derived-right-exact-tensor-comparison: existing 'Normalized tensor comparison for a right exact strong monoidal functor'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-semilinear-derived-calculus: existing 'Ordinary derived semilinear calculus interfaces'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-point-integral-completed-tensor-comparisons: existing 'Completed integral point tensor and scalar squares'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-completed-tensor-rational-naturality: existing 'Naturality and rationalization of a completed tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-semilinear-geometry-derived: existing 'Derived geometric system operations and normalization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-ringed-finite-free-tensor-complex: existing 'Actual scalar tensor comparison on complexes and K-flat preservation'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-rational-compatibility: existing 'Canonical rational point tensor, unit, and scalar compatibility'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-evaluation-tensor-coherence: existing 'Signed tensor coherence for point sections'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-comparison-open-tensor-coherence: existing 'Etale/pro-etale comparison respects the canonical open tensor map'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-evaluation-scalar-data: existing 'Balanced scalar comparison for point sections'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-reduction: existing 'Canonical module scalar tensor data and finite reduction squares'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-slice-evaluation-transpose: existing 'Slice restriction preserves evaluation for an arbitrary dualizing object'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-coef-etale-tensor-model-comparison: existing 'Unique flat-model normalization of the étale scalar tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-open-operation-models: existing 'Open operation comparisons with fixed tensor models and right square'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-finite-source-constraints: existing 'The finite point source uses the recorded tensor constraints'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-evaluation-tensor-data: existing 'Normalized tensor presentation for point sections'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-finite-coefficient-site-hom-arrow: existing 'Canonical finite coefficient site internal-Hom arrow'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-slice-koszul-coherence: existing 'Normalized slice restriction preserves Koszul exchange'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-point-fibre-derived-tensor: existing 'The point fibre functor preserves derived tensor at all coefficient stages'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-evaluation-derived-compatibility: existing 'Representative-normalized derived point comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-coef-ringed-pullback-hom-evaluation-comparison: existing 'Evaluation-defined Hom comparison for ringed pullback'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-semilinear-system-models: existing 'Generic strict semilinear system constructions and representative normalization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-models: existing 'Canonical integral representative normalization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-finite-coefficient-site-scalar-arrow: existing 'Canonical finite coefficient site scalar comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-finite-coefficient-site-chain-tensor: existing 'Canonical finite coefficient site comparison on total tensor complexes'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-system: existing 'Strong symmetric tensor comparison data for the point fibres'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-semilinear-geometry-ops: existing 'Canonical geometric mate and projection words'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-fibre-tensor-finite-models: existing 'Canonical finite point tensor normalization on K-flat representatives'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-etale-native-tensor-pullback: existing 'Native unbounded derived tensor commutes with etale inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-point-ringed-evaluation-model: existing 'Ringed geometric-point evaluation with signed tensor and coefficient models'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-integral-line-tensor-comparison-representative: existing 'K-flat line tensor models and finite balancing'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-coef-semilinear-operations-existence: existing 'Geometric and coefficient operations on a fixed semilinear system calculus'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-coef-semilinear-system-existence: existing 'Ordinary semilinear system calculus and cartesian internal Hom'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-semilinear-geometry-base: existing 'Geometry base fields for coefficient linear operations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-integral-scalar-square: existing 'The integral point completion commutes with scalar extension'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-point-finite-tensor-comparisons: existing 'Finite point tensor comparisons and all quotient squares'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-point-field-tensor-descent: existing 'Rational and common-field point tensor descent'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-point-evaluation-scalar-coherence: existing 'Tensor square for balanced point scalar data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-coef-ringed-tensor-hom-model: existing 'Canonical closed tensor-Hom representative model on a ringed site'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-generator-reduction-coherence: existing 'Basic generator coefficient squares in semilinear systems'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sf-open-restriction-completeness: existing 'Completeness and the actual completion unit after ordinary open restriction'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sf-open-normalization-data: existing 'Geometric and operation data for open tensor normalization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-internal-scalar-tensor-comparison: existing 'Scalar-unit normalized tensor comparison for internal modules'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-internal-extension-monoidal: existing 'Scalar-unit normalized strong monoidal extension of internal scalars'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-derived-tensor-diagrams: existing 'Coherence equations for explicit canonical derived comparison maps'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-derived-tensor-lift: existing 'Symmetric monoidal coherence of a canonical derived tensor lift'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-scalar-tensor-tower-comparison: existing 'Simultaneous normalized scalar tensor comparisons with coefficient coherence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-site-point-tensor: existing 'Signed total tensor comparison for normalized stalks'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-ringed-slice-comparison-model: existing 'Normalized ringed slice comparison data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-scalar-hom-comparison-data: existing 'Actual scalar-adjunction and normalized tensor-Hom comparison data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-geometric-stalk-tensor-constant-single: existing 'Geometric stalks commute with derived tensor against a constant module'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-comparison-tensor-adjunction: existing 'Tensor and adjunction compatibility of canonical ringed-topos path comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-ringed-projection-coherence-data: existing 'Recorded data for tensor projection coherence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-site-point-acyclic: existing 'A conservative point family detects acyclicity'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-derived-two-iso-comparison: existing 'Specified geometric 2-isomorphism comparison on derived modules'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-etale-stalk-total-tensor-comparison: existing 'Canonical signed total tensor stalk comparison and chain naturality'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-exact-completed-koszul-pullback: existing 'Exact product-preserving inverse image transports the actual Koszul unit'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-projection-comparison-etale-proetale: existing 'Etale-to-proetale comparison of the canonical direct-image projection morphism'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-scalar-internal-hom-tower-coherence: existing 'Coefficient-tower and identity coherence for normalized internal Hom'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-proetale-trace-coefficient-interfaces: existing 'Canonical internal-module trace coefficient interfaces'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sfb-ringed-derived-comparison-data: existing 'Data of normalized derived monoidal comparisons of ringed topoi'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-internal-extension-preserves-flat: existing 'Extension of scalars preserves flat internal modules'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-projection-tensor-structure: existing 'Canonical tensor structure in arbitrary recorded presentations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-projection-pullback-comparisons: existing 'Normalized identity, composition and section pullback comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-projection-tensor-compatibility: existing 'Tensor constraints and compatibility of normalized comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-hom-flat-scalar-evaluation-model: existing 'Flat scalar evaluation on an arbitrary first complex and its derived coherence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-projection-first-shift: existing 'The ringed projection mate commutes with shifts in its direct-image input'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-scalar-hom-tensor-coherence: existing 'Tensor coherence of the normalized scalar extension maps'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-scalar-tensor-comparison: existing 'Derived scalar tensor comparison on all K-flat representatives'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sfb-ringed-derived-monoidal-comparisons: existing 'Monoidal and adjunction normalization of derived ringed-topos comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-pullback-resolving-computation: existing 'Derived pullback computes on resolving complexes with independent universes'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-mate-exact: existing 'Exactness data for the ringed-topos projection mate'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: existing 'Derived tensor comparison for arbitrary ringed topoi'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: existing 'Normalization-compatible evaluation of actual local Isom sheaves'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: existing 'Canonical shifts and action units of the derived pullback tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-cochain-pullback-tensor-shift: existing 'The prescribed cochain pullback tensor comparison commutes with both signed shifts'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-square-tensor-compatibility: existing 'Tensor compatibility of a ringed square on flat K-flat representatives'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-normalized-origin-comparison-coherence: existing 'Comparison reduction respects canonical scalar units and composition'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-exchange-tensor-coherence: existing 'Projection-formula coherence for a square of ringed topoi'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-resolving-representative-whiskering: existing 'Restriction to resolving representatives is fully faithful'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-augmented-diagram-projection-mate: existing 'Projection mate for an augmented coefficient diagram before taking inverse limit'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-weil-pbc-normalized-origin-scalar-comparisons: existing 'Canonical quotient scalar-extension unit and associator'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-restriction: existing 'Localization comparisons for the ringed projection mate'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-pulled-reduction-normalization-comparison: existing 'Successive quotient normalizations under the pulled reduction comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-finite-reduction-pullback-coherence: existing 'Finite reduction and the canonical pullback square'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: existing 'Derived pullback computes K-flat tensor representatives'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-augmented-cech-tensor-pullback: existing 'Augmented Cech tensor actions commute with derived inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-weil-pbc-ringed-projection-restriction-data: existing 'Normalized ringed projection and slice comparison data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-reduction-pullback-derived-tower: existing 'Normalized derived pullback of a strict coefficient reduction tower'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: existing 'Canonical tensor comparison unit uniqueness'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-tensor-shifts: existing 'Signed shifts of an already normalized tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-constant-derived-normalization-universal: existing 'Constant derived realization preserves universal coefficient arrows'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-tensor-comparison: existing 'Descent and signed shifts of the normalized pro-etale tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-slice-comparisons-shift: existing 'Shift normalization of canonical ringed-slice comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-global-model: existing 'Existence of the canonically normalized global projection package'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-projection-local-model: existing 'Localization of a normalized global projection package'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: existing 'Canonical tensor comparison unit existence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-tensor-comparison-descent-representatives: existing 'Unique descent of tensor comparison from representatives'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-normalized-derived-isomorphism-transport: existing 'Universal normalization and evaluation of source-site local Isom sheaves'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-ringed-equivalence-module-hom: existing 'Module and closed Hom transport under a ringed equivalence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-derived-adjunction-shift: existing 'Canonical derived ringed-topos adjunction is shift-compatible'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-weil-pbc-ringed-tensor-square-presentation: existing 'Representative presentation of a commutative ringed tensor square'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-weil-pbc-derived-scalar-extension-local-systems: existing 'Coherent localized derived scalar extension and comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-completed-pullback-tensor-comparison: existing 'Canonical completed, rational and common-stage tensor pullback comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sp-open-scalar-operations: existing 'Constant-ring pro-etale scalar and open operations and their canonical comparisons'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-scalar-tensor-unit: existing 'Scalar action unitor for a normalized signed tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-geometric-scalar-association-cocycle: existing 'Scalar-association cocycle from normalized inverse-image restriction squares'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-ordinary-line-derived-scalar-comparison: existing 'Ordinary unbounded derived scalar extension intertwines signed line tensor and evaluation'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-scalar-pullback-representative-data: existing 'Canonical scalar/pullback representative data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sp-semilinear-constant-ring-operations: existing 'Constant-ring semilinear system operations and normalized evaluation mates'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-signed-line-derived-base-change: existing 'Signed line comparisons and their unbounded derived tensor action'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-line-restrictions: existing 'Completeness and normalized restricted line equivalences'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-module-tensor-composition-equation: existing 'Ordinary tensor square for composite module pullback'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-proetale-tensor-coefficient-resolution-square: existing 'Coefficient-resolution square for exact pro-etale tensor pullback'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-tensor-transition-compatibility: existing 'Quotient compatibility of the normalized total tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-adic-site-strict-quotient-interface: existing 'Small-site adic strict quotient interface and canonical normalizations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-normalized-tensor-constraint-transport: existing 'Transport of normalized tensor constraints through coherent realization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-canonical-open-scalar-tensor-models: existing 'Canonical scalar tensor models compatible with open inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-canonical-coefficient-system-geometry: existing 'Geometric realization on the literal constant finite coefficient tower'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-cochain-coefficient-arrows: existing 'Canonical scalar-association and transition arrows on cochain sheaves'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-proetale-restricted-tensor-finite-local-constancy: existing 'Finite local constancy of a restricted tensor with bounded-above inputs'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-exact-pullback-signed-comparison: existing 'Exact ringed pullback identifies the canonical signed derived tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-support-site-comparison: existing 'Etale-proetale comparison for supported sections and their exterior products'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-line-reduction-restriction: existing 'Signed line reductions and restriction to the derived-complete integral category'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-cochain-pullback-tensor-coherence: existing 'Signed tensor comparison and composition on cochain sheaf pullbacks'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-kun-inverse-image-monoidal: existing 'Monoidality of the derived inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sp-open-coefficient-adjunction-data: existing 'Intrinsic open coefficient adjunction data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-etale-scalar-pullback-existence: existing 'Existence of normalized derived scalar/pullback comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sp-open-scalar-tensor-data: existing 'Open scalar tensor normalization data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-etale-scalar-pullback-iso: existing 'Canonical derived scalar and pullback isomorphism'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-cochain-tensor-coherence-data: existing 'Canonical cochain ringed-pullback and coherence data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-kun-constant-projection-morphism: existing 'Canonical constant-coefficient derived projection morphism'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-scalar-extension-tower-coherence: existing 'Coherent quotient towers for integral scalar extension'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-proetale-scalar-tensor-normalization: existing 'Underlying tensor normalization of pro-etale scalar and inverse-image comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-kun-geometric-point-pullback-tensor-normalization: existing 'Tensor normalization of the pullback/stalk evaluation comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-common-stage-tensor-line-coherence: existing 'Natural associativity and regular right unit for common-stage tensor'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-finite-pullback-tensor-comparison: existing 'Canonical finite derived pullback tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-system-tensor-mate-arrows: existing 'Canonical tensor and proper/open arrows for varying coefficient systems'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-supported-constructible-origin-comparison: existing 'Supported constructible etale origin and its unbounded coefficient tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-open-projection-scalar-comparison: existing 'Scalar restriction of the normalized open projection'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-fix-proper-etale-origin-scalar-data: existing 'Canonical scalar, tensor and direct-image comparisons at etale origins'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-open-scalar-coefficient-coherence: existing 'Coefficient coherence of scalar pullback'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-derived-pullback-tensor-iso: existing 'Derived pullback commutes with derived tensor product on the constructible categories'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-sp-proetale-scalar-mate-identifications: existing 'Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-ambient-operation-models: existing 'Ambient completion presentations for integral pullback and tensor'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-strict-coefficient-comparison-calculus: existing 'Simultaneous strict coefficient comparisons on ring-sheaf towers'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-scalar-tensor-pullback-normalization: existing 'Scalar/tensor pullback normalization on a K-flat representative'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-fix-ringed-scalar-tensor-monoidal: existing 'Normalized strong monoidality of derived scalar extension in independent universes'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-system-tensor-reduction-formula: existing 'Tensor formula for actual semilinear reduction adjoints'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-constant-native-pullback-monoidal: existing 'Canonical native derived tensor comparison for constant coefficients'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-exc-proetale-constant-support-projection: existing 'Constant-coefficient projection for compact support'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-kun-geometric-point-projection-comparison: existing 'Geometric-point projection morphism agrees with the constant-section projection morphism'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-cochain-comparison-monoidal-equations: existing 'Monoidal equations for the canonical cochain pullback comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-flat-term-kflat-tensor-native: existing 'Total tensor of native flat-term K-flat complexes'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-kun-derived-pullback-composition-monoidal: existing 'Canonical derived etale inverse-image composition is monoidal'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-open-coefficient-normalizations: existing 'Exact-pullback and open-unit coefficient normalizations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-coherence-tower: existing 'Coherence identities on normalized integral comparison towers'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-cochain-coefficient-universe-transport: existing 'Canonical common-universe transport of ring and module sheaves'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-etale-scalar-pullback-uniqueness: existing 'Uniqueness of normalized derived scalar/pullback comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-line-derived-comparisons: existing 'Normalized derived signed-line reductions and support'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-scalar-hom-comparison-tower: existing 'Evaluation-defined scalar Hom maps respect coefficient towers'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-tower-limit-comparison: existing 'Derived limit of the strict integral comparison tower'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-varying-ring-tensor-comparison: existing 'Normalized tensor comparison for one varying-ring inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-kflat-total-tensor-model: existing 'K-flat total tensor model for flat-term resolutions'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-etale-chart-comparison-isos: existing 'Canonical site comparisons for scalar and chart operations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-sp-intrinsic-open-projection-invertible: existing 'Intrinsic open projection inverse is invertible'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-system-normalized-tensor-closure: existing 'Normalized semilinear systems are closed under tensor and inverse image'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-module-tensor-coefficient-equations: existing 'Ordinary module tensor equations for coefficient change'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-tensor-reduction-tower-comparison: existing 'Strict tensor comparison for finite coefficient-reduction towers'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-integral-line-power-comparisons: existing 'Signed power scalar comparisons and evaluations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-fix-tensor-pullback-square: existing 'Tensor inverse-image comparisons commute around an open square'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pur-integral-line-reduction-data: existing 'Signed integral line reduction and restriction data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pur-normalized-operation-system-models: existing 'Normalization and simultaneous models for finite coefficient-system operations'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pd-section-derived-realization: existing 'Canonical derived section-module realization'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pd-module-ringed-topos-derived-comparison: existing 'Module-object and ringed-topos derived tensor comparison'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs def-pd-section-derived-tensor-data: existing 'Canonical derived section-module tensor data'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-signed-twist-site-transport vs lem-pd-section-derived-tensor-normalization: existing 'Derived tensor and actual pullback tensor arrows under section equivalence'; the remaining claim is the mixed-sign multiplication and negative evaluation/geometric square for the fixed root/projection Tate comparison; root and positive descent are reused inputs.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-open-restriction-comparison-augmentation: the existing result compares open restrictions of augmented injective resolutions and explicitly excludes supported/global comparison; the new delta compares closed-source multiplication on weakly etale tests.

lem-pur-unit-kummer-two-site-normalization vs lem-sfb-unit-binomial-derivative-presentation: the existing result is an explicit polynomial quotient-algebra isomorphism identifying a Kummer cover with a standard derivative presentation; the new result is a degree-one cohomology class and its two-site coefficient normalization.

lem-pur-signed-twist-site-transport vs lem-amb-finite-root-site-comparison: the root map and r=1 geometric square are now cited inputs, not new conclusions; the new claim extends the fixed comparison through mixed-sign multiplication and negative evaluation.

lem-pur-signed-twist-site-transport vs lem-amb-finite-tate-site-descent: the nonnegative comparison is now a cited input; the new conclusions concern negative twists and mixed-sign multiplication and the frame coefficient map.

lem-pur-signed-twist-site-transport vs lem-pur-signed-line-derived-base-change: the existing result constructs the evaluation-normalized signed family for a generic ringed-site functor; the new result checks mixed-sign multiplication and the geometric/site square for the specified projection-normalized finite Tate family.

lem-pur-signed-twist-site-transport vs lem-asd-normalized-signed-tensor-family: the existing result normalizes a tensor family in a single monoidal closed category; the new result is compatibility of a fixed site comparison and geometric pullback for that family.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-etale-closed-constant-tensor: all etale source properties are now cited inputs; the new statement has only the weakly etale section formula and site/pro-etale multiplication squares.

lem-pur-closed-source-site-tensor-comparison vs lem-pur-supported-constant-exchange-normalization: q,b existence/normalization and their geometric/site square are now cited inputs; the new claim compares the actual intersection multiplication and evaluates q sectionwise.

lem-pur-supported-source-system-cup-calculus vs lem-pur-shifted-tensor-morphism-calculus: B and t are reused by citation; the new theorem adds source/target multiplication systems and normalized b/tau cancellation.

lem-pur-unit-kummer-two-site-normalization vs lem-pur-kummer-additivity: the existing class is the Picard H1(G_m)-to-H2(mu) first Chern class for finite-type schemes; the new class is the units H0(G_m)-to-H1(mu) boundary on arbitrary schemes.

lem-pur-signed-twist-site-transport vs lem-asd-finite-etale-tate-line-comparison: the existing result is the root coefficient line and its identity/composition normalization; the new claim is the mixed-sign and negative dual extension for both sites.

## What could not be finished

No stage-1 requirement remains intentionally open. Proofs of the four statement-only tasks are left to the DAG queue as requested, not asserted as Lean proofs. Current dry run and delivery results will be recorded after the checks finish.

## Original arguments retained verbatim

### Original Step 1

Put $m=\ell^n$ and $R=\mathbf Z/m$. Since $\ell\in(\varpi_E)$, $mA=0$, and $m$ is invertible on every $k$-scheme. On the etale site use $L_X=\mu_{m,X}\otimes_R A_X$ and its tensor powers and duals. [lem-asd-etale-finite-twist-pullback] gives the rank-one line property and the canonical pullback identifications, including all integer twists and their tensor, evaluation and composition compatibilities. The projection-induced identification in [def-pur-frame-class], justified there by [lem-pur-twist-sheaf-locally-free], identifies the pro-etale twist $A_X(1)$ with $\mu_{m,X}\otimes_R A_X$. Identical root formulas on etale objects identify the inverse image of the etale roots with the pro-etale roots, i.e. the adjoint map $\rho_X:\nu_X^{-1}\mu^{\mathrm{et}}_{m,X}\to\mu_{m,X}$ of [def-pur-frame-class] is an isomorphism. Indeed, on an etale cover trivializing the roots by a primitive root $\zeta$, both root sheaves become the constant sheaf $R$, both maps send a locally constant exponent $a$ to $\zeta^a$, and by [lem-sf-comparison-pullback-exact](1) (with $\Lambda=R$) $\nu^{-1}R_{\mathrm{et}}\cong R_{\mathrm{proet}}$ as sheaves of rings; so on each member of the cover $\rho_X$ is an $R$-linear map between copies of $R$ sending $1$ to $1$, hence this isomorphism, on every pro-etale object over that member. In degree zero this agrees on etale objects with the section comparison [lem-cbc-abelian-etale-proetale-cohomology-comparison]. The tensor identification then sends $\zeta^a\otimes b$ to the same local scalar $ab$ on both sites, so these identifications agree on overlaps. Tensor powers and dual evaluation give the same assertion for $A(r)$, $r\in\mathbf Z$. Every such sheaf is flat: locally tensoring with it is tensoring with $A$; its inverse is tensor with its dual.

Uses: def-pur-frame-class, lem-asd-etale-finite-twist-pullback, lem-pur-twist-sheaf-locally-free, lem-cbc-abelian-etale-proetale-cohomology-comparison, lem-sf-comparison-pullback-exact

Source: literature/stacks-project/sites-cohomology.tex; Tags 03PL (etale-cohomology.tex, lemma-kummer-sequence), 07A4 (lemma-pullback-tensor-product); concrete finite twist prescription in def-pur-frame-class

### Original Step 2

First work on the etale site. For $i:C\hookrightarrow X$ put $P_C=i_*A_C$. Apply [lem-pur-etale-closed-constant-tensor] with the finite ring $A$ of Step 1. Its specified $b_{v,C}$ is the adjoint of pullback of locally constant sections and is an isomorphism for every $v:X'\to X$. Its identities and composition equations apply also to nonreduced and empty supports. The same lemma supplies flatness of every $P_C$ and the particular isomorphism $\mu_{C,D}:P_C\otimes_A^LP_D\xrightarrow{\sim}P_{C\times_XD}$ induced by restriction and multiplication. Use these maps to define the etale analogue of the tensor-morphism construction in [def-pur-supported-cup], which itself is pro-etale. The associativity, symmetry and pullback equations for these source multiplications are exactly the equations in the cited lemma. They are the source equations used in Steps 4--6; they assert ordinary coefficient pullback and do not use exceptional base change. For the normalized etale closed-source exchange, specialize the existing underived finite base-change isomorphism [sk-lem-pbc-finite] to the tensor unit, identify constant pullback with the monoidal unit map, and use epimorphic constant restriction for uniqueness.

Uses: lem-pur-etale-closed-constant-tensor, def-pur-supported-cup, sk-lem-pbc-finite

Source: literature/stacks-project/sites-cohomology.tex; Tag 03Q1 (etale-cohomology.tex, lemma-stalk-pullback); blueprint lemma-weil-pbc-finite-stalk-formula (geometric finite stalk formula), and the explicit coefficient multiplication of def-pur-supported-cup; the exactness of geometric stalks and tensor-stalk formula and flat-term K-flat descent; etale analogue constructed here rather than attributed to the pro-etale definition

### Original Step 3

Here are the tensor constraints used in the calculations, including their signs. Sheaf tensor is additive and symmetric monoidal by [lem-pc-sheaf-modules-tensor-closed]. On total complexes [def-pc-tensor-complex-sheaves], the associator is $((x\otimes y)\otimes z)\mapsto x\otimes(y\otimes z)$ and the symmetry is $x\otimes y\mapsto(-1)^{pq}y\otimes x$ for $x,y$ in cochain degrees $p,q$. The latter is a chain map: the coefficients of $dy\otimes x$ on its two sides are $(-1)^{pq}$ and $(-1)^{p+p(q+1)}$, and those of $y\otimes dx$ are $(-1)^{(p+1)q}$ and $(-1)^{pq+q}$; each pair agrees. These maps are natural, and the associator, unit and symmetry equations hold on pure tensors. K-flat flat-term resolutions compute the derived tensor and determine its transformations by [lem-weil-pbc-site-derived-tensor-descent]. The displayed constraints therefore give the same constraints on derived tensors. For three factors one can apply this assertion successively: the tensor of two K-flat complexes is K-flat, since tensoring an acyclic complex first with one and then the other is acyclic; its terms are flat since tensor products of flat sheaves are flat and the total terms are countable direct sums of them, using [lem-pc-kflat-closure]. The canonical pullback tensor comparisons of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] respect these constraints and shifts: on flat-term models both routes pull back the same pure tensor with the same degree and sign, and the preceding descent uniqueness gives equality on derived categories. This argument applies to either small site and to the comparison morphism between them.

Uses: lem-pc-sheaf-modules-tensor-closed, def-pc-tensor-complex-sheaves, lem-weil-pbc-site-derived-tensor-descent, lem-pc-kflat-closure, lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Source: literature/stacks-project/sites-cohomology.tex; Tags 07A4 (lemma-pullback-tensor-product), 0FPL (lemma-cup-product-associative), 0FPM (lemma-cup-product-commutative): tensor-constraint calculation, with the omitted commutativity calculation supplied

### Original Step 4

By [lem-amb-closed-support-hom] represent a class by $\alpha:P_C\to A_X(r)[a]$. Exact inverse image [prop-weil-pbc-inverse-image-modules-exact] defines
$$v^*\alpha=\tau_{v,r}[a]\circ v^{-1}(\alpha)\circ b_{v,C}^{-1}.$$
Here $\tau$ is Step 1 and $b$ is Step 2. To fix its normalization, apply $\operatorname{Hom}(-,I^q)$, for injective $I^q$, to the source sequence of [lem-weil-pbc-open-closed-short-exact]. Evaluation at the image of $1$ identifies $\operatorname{Hom}(P_C,I^q)$ with $\ker(I^q(X)\to I^q(U))$; the last Hom is $I^q(U)$ by [lem-weil-pbc-extension-by-zero-adjunction]. For $a<0$ both groups vanish, since the coefficients are degree-zero sheaves and supported cohomology is a right derived functor. For $a\geq0$, [lem-weil-pbc-ext-exact-functor-cocycle] represents the displayed derived map by inverse image followed by the injective comparison. Evaluating at $1$ gives precisely pullback of a supported section, so [lem-weil-pbc-site-cohomology-pullback] identifies it with the usual kernel pullback. Functoriality of [thm-pur-with-support-exactness] now gives restriction and boundary compatibility. The equations for $b$ in Step 2 and for $\tau$ in Step 1 give identities and composition. When $C=X$, $P_C=A_X$ and $b$ is the constant-ring identification, so the formula is ordinary pullback. The zero composite in the coefficient short complex follows by the open-extension adjunction from disjoint-support vanishing [lem-sfb-proetale-open-disjoint-direct-image] on the pro-etale site and its existing etale counterpart.

Uses: lem-amb-closed-support-hom, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-open-closed-short-exact, lem-weil-pbc-extension-by-zero-adjunction, lem-weil-pbc-ext-exact-functor-cocycle, lem-weil-pbc-site-cohomology-pullback, thm-pur-with-support-exactness, lem-sfb-proetale-open-disjoint-direct-image

Source: literature/stacks-project/sites-cohomology.tex; Tag 09XP (etale-cohomology.tex, section-cohomology-support); Tag 0G78 (cohomology.tex, remark-support-functorial); explicit pullback on supported morphisms

### Original Step 5

Use $\operatorname{cup}(\alpha,\beta)=t_{a,b}(\alpha\otimes^L\beta)\mu_{C,D}^{-1}$, followed by $A(r)\otimes_A A(s)\cong A(r+s)$. This is the etale analogue of [def-pur-supported-cup], with Step 2's etale source isomorphism. Apply [lem-pur-shifted-tensor-morphism-calculus] to the flat sources $P_C,P_D$ and targets $A(r),A(s)$. Its $t_{a,b}$ uses the same sign $(-1)^{bp}$ as that definition. Its biadditivity gives bilinearity after composing with $\mu^{-1}$. Its associativity equation, together with Step 2's associative source multiplication and Step 1's twist multiplication, makes the two triple products equal. Its symmetry equation gives $(-1)^{ab}$; Step 2 identifies the symmetric source maps, and the twist symmetry identifies the target with $A(r+s)$. This is the required graded symmetry, for all integer degrees.
For pullback, apply the same lemma with $u^*=v^{-1}$, exact by [prop-weil-pbc-inverse-image-modules-exact]. Its pullback equation identifies the image of $t_{a,b}(\alpha\otimes\beta)$ with $t'_{a,b}(v^{-1}\alpha\otimes v^{-1}\beta)$. Substitute Step 4's formula for each pulled-back class. Step 2's equation $b_{v,C\cap D}v^{-1}\mu_{C,D}=\mu_{C',D'}(b_{v,C}\otimes b_{v,D})$ cancels the source identifications. Step 1 identifies the twist targets. The resulting composite is exactly $v^*\alpha\cup v^*\beta$.

Uses: def-pur-supported-cup, lem-pur-shifted-tensor-morphism-calculus, prop-weil-pbc-inverse-image-modules-exact

Source: literature/stacks-project/sites-cohomology.tex; Tags 0FPL and 0FPM (associativity and commutativity), with the supported tensor-morphism calculation in place of an appeal to an ordinary-cohomology product

### Original Step 6

We identify the closed-support source objects under site comparison for arbitrary schemes; this avoids imposing a quasi-compactness condition on $X\setminus C$. For every weakly etale $y:Y\to X$, [lem-cbc-comparison-pullback-sections] identifies
$$(\nu_X^{-1}P_C)(Y)=\Gamma(Y_{\mathrm{et}},y^{-1}P_C).$$
Step 2 applied to $y$ identifies the right side with $\Gamma((Y\times_XC)_{\mathrm{et}},A)$. Degree-zero [lem-cbc-abelian-etale-proetale-cohomology-comparison] identifies this with $\Gamma((Y\times_XC)_{\mathrm{proet}},A)$, which is $(i_*A_C)(Y)$ by [def-weil-proetale-module-direct-image]. All maps are induced by pullback of locally constant sections, so they commute with restrictions in $Y$, addition and scalar action. Hence they define $q_C:\nu_X^*P_C\xrightarrow{\sim}P_C^{\mathrm{proet}}$, taking the image of $1$ to the image of $1$. The comparison is exact and identifies constant rings by [lem-sf-comparison-pullback-exact]. The tensor comparison of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], together with $q_C,q_D,q_{C\cap D}$, identifies the etale source multiplication of Step 2 with precisely the pro-etale source multiplication $\mu$ specified by [def-pur-supported-cup]: both maps restrict two locally constant sections and multiply them. The equality on sheaf generators gives the equality on flat-term models, hence on derived tensors by [lem-weil-pbc-site-derived-tensor-descent]. In particular this compares the auxiliary etale product with the current pro-etale definition, rather than taking an etale construction from that definition. The latter supplies the pro-etale flatness and coefficient isomorphism directly; no geometric-stalk conservativity is asserted for pro-etale sheaves. Flatness and K-flatness of these pro-etale source objects follow as well from preservation of flat-term K-flat models by the cited ringed-topos lemma.

Uses: lem-cbc-comparison-pullback-sections, lem-cbc-abelian-etale-proetale-cohomology-comparison, def-weil-proetale-module-direct-image, lem-sf-comparison-pullback-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-site-derived-tensor-descent, def-pur-supported-cup

Source: literature/stacks-project/sites-cohomology.tex; Tags 099V/099W (proetale.tex, relative and cohomology comparison), 09A5 (proetale.tex, section-morphism), 07A4 (tensor pullback); the sectionwise closed-constant comparison

### Original Step 7

Full faithfulness in [thm-weil-pbc-site-comparison], with Steps 1 and 6 and the Hom descriptions [lem-pur-supported-hom, lem-amb-closed-support-hom], gives a bijection on supported groups: $\alpha\mapsto\nu_X^*(\alpha)q_C^{-1}$, with twists identified. By [lem-weil-pbc-comparison-pullback] it commutes with geometric pullback: $q_C$ and $b_{v,C}$ both pull back the same local section.
For localization, use [lem-cbc-proetale-extension-zero-comparison] to identify $\nu_X^*j^{\mathrm{et}}_!A_U$ with $j^{\mathrm{proet}}_!A_U$. This canonical comparison carries counits to counits: under the two adjunctions [lem-weil-pbc-extension-by-zero-adjunction, lem-cbc-proetale-extension-zero], both maps correspond to the identity of $A_U$, since comparison restricts on etale objects to the same sections. Step 6 identifies the other arrow $A_X\to P_C$ by its value on $1$. Exact comparison [lem-sf-comparison-pullback-exact] therefore sends [lem-weil-pbc-open-closed-short-exact] to the identical source sequence on the pro-etale site. By [lem-weil-pbc-exact-functor-ses-triangle-image] it sends its connecting arrow to the connecting arrow with the same sign. Applying Hom into the coefficient object thus commutes with the localization boundary; Step 4's kernel evaluation and [thm-pur-with-support-exactness] fix its normalization.
Finally [lem-pur-shifted-tensor-morphism-calculus] and Step 6's multiplication comparison identify the specified cup of [def-pur-supported-cup], including its shift sign, with the etale cup. Every pro-etale class is in the Hom bijection, so all laws in Steps 4--5 hold on both sites. In Lean, use [lem-sf-open-comparison-unit-normalization] to identify the extension comparison with the specified inverse-image comparison. Transport its unit equation to the inverse-image adjunctions; the triangle identities give the counit equation. This identifies both arrows of the exact comparison image of the etale coefficient sequence, so its pro-etale image is short exact without a quasi-compactness assumption on the open. Open pullback exchange is then the unique isomorphism of the kernels of the closed restriction arrows, obtained from exact inverse image and the normalized middle and closed-source isomorphisms.

Uses: thm-weil-pbc-site-comparison, lem-pur-supported-hom, lem-amb-closed-support-hom, lem-weil-pbc-comparison-pullback, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-extension-by-zero-adjunction, lem-cbc-proetale-extension-zero, lem-sf-comparison-pullback-exact, lem-weil-pbc-open-closed-short-exact, lem-weil-pbc-exact-functor-ses-triangle-image, thm-pur-with-support-exactness, lem-pur-shifted-tensor-morphism-calculus, def-pur-supported-cup, lem-sf-open-comparison-unit-normalization

Source: literature/stacks-project/sites-cohomology.tex; Tags 09B1 (proetale.tex, lemma-compare-derived), 09XP (etale-cohomology.tex, support), 095L (open-closed sequence); comparison of the actual boundary using the source short exact sequence

### Original Step 8

It remains to check the specified Kummer classes, rather than an abstract class assumed to satisfy the desired laws. By [lem-amb-kummer-any-base] the exponent-$m$ Kummer sequence is short exact on every scheme under consideration. Its boundary $\delta_X:\Gamma(X,\mathcal O_X)^\times\to H^1(X_{\mathrm{et}},\mu_m)$ is a homomorphism by [lem-weil-pbc-right-derived-universal-delta-functor]. Therefore $\delta_X(uw)=\delta_X(u)+\delta_X(w)$. For $v:X'\to X$, pullback of functions gives maps $v^{-1}\mathbf G_{m,X}\to\mathbf G_{m,X'}$ commuting with $m$-th powers and carrying roots to roots. Together with $v^{-1}\mu_{m,X}\cong\mu_{m,X'}$ from [lem-asd-etale-finite-twist-pullback], these are a morphism from the inverse-image Kummer sequence to the Kummer sequence on $X'$. Its maps on degree-zero global sections send $u$ to $v^*u$. [lem-weil-pbc-site-cohomology-pullback], followed by naturality of the connecting homomorphism under a morphism of short exact sequences, gives $v^*\delta_X(u)=\delta_{X'}(v^*u)$. The coefficient map is $z\mapsto z\otimes1_A$; pulling it back gives that identical map on $X'$ by the tensor comparison and the root identification in Step 1. Hence applying it to $\delta$ proves both Kummer identities on the etale site. On the pro-etale site [def-pur-frame-class] defines $\kappa_X(u)$ by first comparing this etale boundary class and then applying the projection-induced roots-to-twist map. Step 1 identifies this coefficient map on the two sites, and the comparison and geometric pullbacks commute by [lem-weil-pbc-comparison-pullback] and the composition law of [lem-weil-pbc-site-cohomology-pullback]. Both Kummer identities therefore hold for the concrete pro-etale class as well. This also shows its compatibility with the supported boundary and the cup operations already compared in Step 7. The argument never tensors $\mathbf G_m$ as an $R$-module and never requires $A$ free over $R$.

Uses: lem-amb-kummer-any-base, lem-weil-pbc-right-derived-universal-delta-functor, lem-weil-pbc-site-cohomology-pullback, lem-asd-etale-finite-twist-pullback, def-pur-frame-class, lem-weil-pbc-comparison-pullback

Source: literature/stacks-project/sites-cohomology.tex; Tag 03PL (etale-cohomology.tex, lemma-kummer-sequence); Tag 01F8 (cohomology.tex, lemma-functoriality); concrete arbitrary-index Kummer class of def-pur-frame-class

