# Stage-1 delivery: lem-sfb-closed-torsion-rigidity-serre-transfer

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-torsion-rigidity-serre-transfer.json`: item, statement unchanged, split in eight steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-finite-complex-heart-filtered-closure.json`: new statement-only node, no Mathlib match. Ambient filtered finite-complex-heart presentation and closure on qcqs schemes.
- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-three-term-scalar-rigidity.json`: new statement-only node, no Mathlib match. Relative comparison for one supported three-term local-model complex.
- `citations.json`: exact statement quotations for every step/node pair.
- `searches.jsonl`: actual search-command records. Existing item searches retained; new searches recorded with their actual results.

## Attachments

None. Searched the live project `lean/WeilConjectures/` by the exact blueprint tag/id and by rigidity, closed immersion, scalar local models, Serre closure, and finite-complex hearts. The closed project declarations about the abstract weak Serre coproduct closure and conditional proper direct-image preservation do not assert this item. The upstream alias search also returned no declaration of the item. Mathlib declarations are not treated as project attachments.

## Sources wanted

WANTED: a proof of qcqs filtered finite-complex-heart ambient closure, with all-continuous norm-topological algebraic-closure coefficients and without a local absolute cohomological-dimension bound, for lem-sfb-qcqs-finite-complex-heart-filtered-closure.

WANTED: a relative torsion-to-topological coefficient theorem for a supported three-term scalar local-model complex and an arbitrary torsion-rigid qcqs closed pair, including norm-topological algebraic-closure coefficients, for lem-sfb-supported-three-term-scalar-rigidity.

The new sources point to the precise current blueprint obligation and explicitly say they are agent-extracted obligations, not literal theorems of Hemo–Richarz–Scholbach or Bhatt–Scholze. I read HRS Corollary 4.4, Lemma 5.3 and Section 8 (especially Lemmas 8.5–8.6), and RTW Theorem 1.2.8 and Proposition 1.3.11. These motivate the decomposition but do not establish the two new nodes in their full stated generality. Their proofs remain future stage-1 items; neither carries a proof sketch inside its statement.

## Problems found and repaired

The item was an unsplit, agent-formulated relative transfer obligation. No incorrect statement was established and its text is preserved. Its source path names the older main-20261015 snapshot; new proof sources use `literature/blueprint/latest/`. I read the latest refinement proof (2) and cocycle proof, the chapter record, and the unit record. The unit record still describes the older smooth-purity compactification argument; I have not changed its route or realized fields because this item is not its key node.

The key gaps were not ordinary devissage: invariance on the generators alone does not prove stability under kernels and cokernels, and abstract abelianness of an Ind category does not prove that its realization is the required ambient weak Serre hull. The new filtered-heart lemma states that realization/closure obligation explicitly. The other new lemma concerns only three local-model terms along a specified finite support path; the item itself performs the finite geometric refinement, localization-sequence assembly, and filtered-colimit passage.

I did not apply the existing affine finite-heart approximation theorem: it assumes affine geometry and a uniform absolute local cohomological bound absent here. I did not apply the existing ind-constructible heart theorems: their finite-type/field/Noetherian settings are absent here. I did not use finite-coefficient étale/pro-étale comparison for an arbitrary topological module. I did not replace all-continuous norm-topological algebraic-closure coefficients by the finite-extension colimit ring.

The original closed pair need not have quasi-compact open complement. Only the finitely many closed arrows introduced in the constructible refinement tree have that property. The proof never uses exactness of direct image along the original closed immersion. Supported rigidity keeps the torsion assumption on the original ambient pair; the proof does not assume it on each stratum.

## Not duplicates

lem-sfb-qcqs-finite-complex-heart-filtered-closure vs lem-sfb-finite-complex-heart-filtered-approximation: the existing node is affine and assumes a uniform cohomological bound on every affine pro-etale test; neither hypothesis is available in this item. The new node states the qcqs presentation/closure obligation without those assumptions and does not cite the existing node as a proof.

lem-sfb-qcqs-finite-complex-heart-filtered-closure vs det-ind-heart-kernels-cokernels: the existing node concerns filtered constructible objects in a separated finite-type field setting; the new node concerns filtered zeroth cohomology of finite constructible complexes, permits nonconstructible finite-stage hearts, and is qcqs without field/Noetherian assumptions.

lem-sfb-qcqs-finite-complex-heart-filtered-closure vs lem-sfb-ind-constructible-heart-continuous: the existing node uses finite-extension rational coefficients and separated finite-type geometry over a field with ell invertible; the new node includes every original coefficient and all qcqs schemes and finite-complex hearts.

lem-sfb-supported-three-term-scalar-rigidity vs lem-sfb-supported-three-term-scalar-cd: the existing node is an absolute upper bound on an affine scheme from local torsion cohomological dimension; the new node is relative isomorphism for a closed pair, without absolute bounds or affine geometry.

lem-sfb-supported-three-term-scalar-rigidity vs lem-sfb-integral-lisse-closed-base-change: the existing node concerns an affine integral morphism and a finite-rank lisse module in a positive-characteristic field setting; the new node concerns a torsion-rigid closed pair and a supported kernel modulo image, with arbitrary maps, general coefficients and qcqs geometry.

lem-sfb-supported-three-term-scalar-rigidity vs lem-sfb-closed-torsion-rigidity-serre-transfer: the new node does not assert rigidity for the weak Serre coproduct hull, nor for arbitrary constructible hearts. It handles one supported three-term finite-local-model configuration. The item still supplies the finite partition tree, exact path sequences, induction, and the filtered-colimit extension.

DAG searches used both full concepts, existing lemma ids, and blueprint_refs searches for rigidity, torsion rigidity, scalar rigidity, finite constructible complex, and ind-constructible. No matching blueprint node was found. No new node introduces a Stacks tag already attached to an existing node. The scalar-cd, heart-closure and coefficient-comparison candidates above were read before deciding the difference.

## Review by NE

I checked delivery-errors B–E against the actual item, both new files, every cited statement and the source passages. Both new statements introduce the prime, coefficient rings/topologies, schemes, sites, universe, module category, finite scalar models, diagrams and maps. They are statement-only, with no proof/proof dependencies, correct provenance and concrete blueprint ancestry. Their searches were run with msearch.py and the returned hits were read. In particular I read Mathlib `CategoryTheory/Abelian/Indization.lean` (it assumes an already abelian small input), `Condensed/AB.lean` (ambient AB axioms), and `AlgebraicGeometry/Sites/ElladicCohomology.lean` (definitions of one coefficient sheaf's cohomology). None identifies the ambient image in the first new node or supplies relative rigidity in the second. Other hits are closed-immersion geometry, locally finite presentation, solid-module definitions, and group cohomology, not matches.

Step 1 uses the actual monoidal point-pullback compositor, the module inverse-image exactness theorem, exact-functor cohomology comparison, and the scalar-model definition. These statements give the coefficient identification, kernels/images comparison, and the same scalar presentation after restriction; they do not assert a finite-field coefficient descent.

Step 2 uses precisely the closure statement of the new qcqs filtered-heart node. Its hypotheses are just the coefficient/site setup and qcqs geometry already present. Intersection minimality then gives the required inclusion. No existing affine absolute-bound theorem is silently substituted.

Step 3 uses the definition's finite constructible partitions and the refinement theorem's actual scheme factoring maps. The root is qcqs and there are just three partitions. Actual factoring maps, rather than set-theoretic containment, justify pulling back their finite local models. There is no uniform scalar-matrix assumption on differentials.

Step 4 uses the ringed pro-etale open–closed exact sequence and exact extension functors only where complements are quasi-compact. This condition is supplied by the refinement theorem for every path. The internal/sectionwise transport node explicitly identifies these functors and exact sequences. The inverse-image theorem gives exactness of the restrictions to the given closed member.

Step 5 uses the exact statement of the new supported rigidity node: ambient T,T_0, the path functor, all three independently trivializable terms and the kernel/image quotient. Its assumption is the original torsion-rigidity hypothesis, not a stronger hypothesis on every test or stratum. In particular I did not assume absolute cohomological dimension. The r=0 case is covered but does not cover the entire weak Serre hull.

Step 6 uses the natural short-exact-complex triangle theorem and the right-derived triangulated theorem. Module sections have the stated additive evaluation meaning. Smallness of the ringed sites permits the K-injective existence result after the exact internal/sectionwise equivalence. Exact inverse image takes a horseshoe resolution sequence to a sequence resolving its pullback; comparison to target injective resolutions and the natural cone boundary give the commuting boundary square for the actual restriction. Bottom-up induction applies the two-outer-vertices criterion to each one of these triangles. No assumption that arbitrary kernels/cokernels of rigid modules are rigid is made.

Step 7 uses the actual module adjunction, the left-adjoint colimit theorem and precisely the qcqs/global-sections clause of bounded-below filtered continuity. Both diagrams consist of degree-zero objects, so their common lower bound is zero even if the finite complexes presenting their hearts have unbounded lengths. Naturality on each colimit insertion proves that the bottom arrow is the actual restriction. Step 8 uses the definition of quasi-isomorphism/localization to retain the derived-form conclusion. These are the statements quoted verbatim in citations.json; no proof-only construction of another node is cited.

Small cases checked for the filtered-heart node: zero complex, a single constructible object in degree zero, zero coefficient ring, an empty scheme, identity/zero maps and arbitrary small coproducts interpreted in the fixed universe. For supported rigidity: the identity closed immersion gives the identity comparison, zero terms and empty leaves give zero, r=0 leaves the unsuppported local-model calculation, and finite coefficients leave an ordinary torsion comparison. The two non-finite rational cases retain the induced topology; no reduction from Omega to a finite extension is asserted. A non-quasi-compact complement for the original closed immersion is allowed throughout.

Every non-elementary fact used in the assembly has a node citation. All proof steps are below 2000 characters. Generic structural citations from other units are recorded in split_report.tool_uses, not top-level tool_uses. No SGA source, new Lean, compiler, Lake or local DAG/preflight checker was used.

## Unfinished work

The split is one level: the two new independent comparison/presentation obligations remain unsplit, with exact full-generality references WANTED as above. This delivery does not assert their proofs are complete or that the entire dependency closure is proved. No Lean attachment or Mathlib leaf is claimed. The item proof is complete relative to their explicitly stated interfaces.

## Validation

The required deliver.py --no-push run exited successfully with OK (not pushed), preflight passed, at 824a142a659. The initial run found a doubled-backslash TeX array-row separator; I replaced the array by two comparison formulas and explicit commutative-square prose. The corrected run passed. A final dry run validates this report update before the direct delivery push. No Lean/compiler/build check was run.
