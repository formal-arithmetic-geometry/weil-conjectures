# NX: lem-per-lisse-tensor-permanence

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-lisse-tensor-permanence.json`: statement, split into four proof steps; original statement retained; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-lisse-cohomology-calculus.json`: new statement-only lemma, unsplit; no Mathlib match. This is a coefficient/cohomology comparison, with no support, dimension or perverse-class assertion.
- `citations.json`: twelve verbatim excerpts, one for every citation of each item proof step.
- `searches.jsonl`: the search command's own log, retained verbatim. All searches were run in this session; none were invented.

The item is not the statement of its Fourier-exactness unit; no unit record is changed.

## Attachments

None. I searched the source tree for the blueprint id and for support/lisse tensor declarations, and read `WeilConjectures/SixFunctors/Etale/Perverse/Operations.lean` lines 70-155. `AlgebraicGeometry.Etale.DerivedCategory.SupportCondition.tensor` (lines 131-136 in this checkout) has `sorry`. The syntactically proved `isPerverseLE_tensor` and `isPerverseGE_tensor` depend on it. `IsLisse.coefficientDual` at lines 121-125 also has `sorry`. Thus no collection of closed project declarations proves all clauses. The audit's older line numbers are offset from the current source; its assessment of the open proofs is still correct. The generic coefficient-category Lean declarations are not an exact statement of the adic finite-rank Qlbar statement. I did not relabel those generic declarations as a completed attachment.

## WANTED

None. The blueprint, Stacks source, and Bhatt--Scholze are available locally. No document was downloaded.

## Corrections and scope

The imported proof had not isolated the adic cohomology calculation and had not justified the shifted assertions. Its phrase “of the same support” fails at rank zero: on a point, take nonzero K and L=0. The tensor is zero. The stated inclusions and the lemma remain true. Step 2 uses containment only, including for empty supports, and does not add a positive-rank hypothesis. This is a proof error, not a STATEMENT-DISPUTED: the item's statement is unchanged.

The old `def-weil-pbc-constructible-complexes` now defines finite-ring etale coefficients only; it does not define the Qlbar objects or lisse Qlbar sheaves used here. I replaced that statement dependency with the actual adic common-stage category, adic lisse-sheaf definition, and coefficient-stage operations, and added the definitions of smoothness and pure dimension. The support setting already imports the conditions on schemes and on the invertibility of ell needed for the adic category. These are not new hypotheses on the target.

I read both the original item and the current main-20261015 item and proof. Their support/duality proof is the same. The current unit still uses the ordinary-cohomology route to Fourier exactness. This subsidiary lisse-tensor lemma does not replace either step of that unit, and its own original support/duality route is retained. No SGA source is used. The closed `lem-per-dual-lisse-tensor` is used only for its statement, not for its imported proof's finite-coefficient trivialization citation.

## Searches and the new lemma

Before creating the new node I searched the whole DAG by lisse, dual, tensor, cohomology, titles, and exact ids, and used `tools/blueprint_refs.py ancestor` and `search` with `lisse`, `lisse-tensor`, `lisse cohomology`, `adic tensor`, `tensor cohomology`, `tensor-cohomology`, `coefficient dual`, and `finite-projective-tensor-hom`. The new id did not exist. The nearest ancestor is the item itself, with no intervening created nodes. The item is not equivalent to another blueprint theorem; the two related lisse-tensor nodes state different assertions. The new calculation has no exact blueprint equivalent, so both same_as lists are empty.

The Mathlib searches are recorded with their exact tool/query strings in the node and command log. I tried the adic cohomology formulation and a general exact-flat-tensor/homology formulation, and separately searched the lisse linear dual formulation. LeanFinder returned light condensed monoidal structures, free sheaf/module constructions, and internal projectivity conditions. LeanSearch also returned ordinary module flatness, ordinary duals, FDRep.dualTensorIsoLinHom, and Functor.preservesHomologyOfExact. These are ingredients in different categories, not one-line specializations giving the theorem for the project's completed integral, rationalized and common-stage categories. I read Mathlib `CategoryTheory/Sites/CartesianMonoidal.lean` lines 25-43: `Sheaf.tensorProd_isSheaf` is cartesian tensor. I read `Algebra/Homology/ShortComplex/PreservesHomology.lean` lines 773-783: the homology isomorphism assumes an already homology-preserving functor. I read `RingTheory/Flat/CategoryTheory.lean` lines 45-105: those theorems concern ordinary modules over a ring. Neither establishes the adic fibre/operation comparisons, the lisse dual, or the strong normalized-tower domain. The first Loogle query reported an unknown identifier; I retained that diagnostic and followed it with the valid `CategoryTheory.Sheaf` and `CategoryTheory.Functor.mapHomologicalComplex` queries. The successful broad grep searches and semantic hits likewise give no exact declaration. The item itself was also searched semantically as perverse support/cosupport permanence.

The source of the new lemma is Bhatt--Scholze, *The pro-etale topology for schemes*, Definition 6.8.1, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4, Definition 6.8.8, Proposition 6.8.14(2), and Remark 6.8.15, read from the local PDF (printed pp. 58-62). The node explicitly does not claim that those pages state its stronger exact-category comparison verbatim. Its remaining obligation includes the comparison with the project's derived-complete, uniformly bounded normalized towers and compatible etale-origin witnesses, not just the Bhatt--Scholze category. This is why it is a genuine unsplit coefficient lemma rather than an elementary extra node or an unjustified identification with discrete non-torsion etale sheaves.

A route for that later split is: work over one finite field of definition; identify lisse sheaves with pro-etale local finite free models and with their finite quotient towers; compute tensor and dual on these models; check the finite-level normalization, etale-origin witnesses and boundedness; then rationalize and check compatibility under finite coefficient extension before passing to the common-stage category. On finite-free models cohomology is a finite direct sum, the dual has the dual basis, and the evaluation pairing is the usual one. The actual comparison with the completed construction and the geometric fibres must be proved, not inferred from the fact that an unrelated exact functor preserves homology. Supporting general ringed-site ingredients can be reused from existing nodes, including `lem-weil-pbc-exact-functor-complex-cohomology`, `lem-sfb-ringed-site-perfect-duality` and `lem-sfb-localized-site-tensor-restriction`, when this new node is split; it has no premature proof steps or proof dependencies.

## Not duplicates

lem-per-adic-lisse-cohomology-calculus vs lem-per-lisse-tensor-permanence: the new node computes adic cohomology/fibres and the linear dual, without a support inequality, perverse condition, smoothness or a dimension hypothesis; the item proves those geometric inequalities, uses Verdier duality, and handles every shifted class.

lem-per-adic-lisse-cohomology-calculus vs lem-per-dual-lisse-tensor: the existing node is the Verdier-dual tensor isomorphism; it does not assert the cohomology/fibre calculation, preservation of the exact adic category, or lisseness of the coefficient linear dual. The item cites the existing Verdier isomorphism directly.

lem-per-adic-lisse-cohomology-calculus vs lem-exc-constant-field-sheaf-tensor-cohomology: the existing node treats termwise tensor of ordinary module-sheaf complexes over a discrete constant field sheaf on a site. It supplies neither the completed/rational/common-stage comparison nor adic fibre/dual statements.

lem-per-adic-lisse-cohomology-calculus vs lem-sfb-etale-derived-tensor-stalk: the existing node is for ordinary derived modules over a discrete constant ring on the small etale site; no adic comparison or completed construction is asserted there.

lem-per-adic-lisse-cohomology-calculus vs lem-weil-pbc-exact-functor-complex-cohomology: the existing node assumes an exact functor between given abelian categories and proves its termwise cohomology comparison. It does not identify the completed/rational/common-stage tensor with such a functor or assert lisse-dual/fibre comparisons.

lem-per-adic-lisse-cohomology-calculus vs lem-weil-pbc-condensed-finite-free-tensor-exact: the existing node asserts preservation of finite limits by an ordinary internal-module tensor functor. It does not identify that construction with the project's stronger adic category or its geometric-fibre functors.

lem-per-adic-lisse-cohomology-calculus vs lem-sfb-ringed-site-perfect-duality: the existing node proves abstract derived duality for a perfect object. It does not give concentration in degree zero for lisse adic objects, identify the ordinary lisse dual, or give the exact-category tensor/cohomology/fibre comparison.

lem-per-adic-lisse-cohomology-calculus vs lem-pod-finite-projective-tensor-hom: the existing node is a derived tensor-Hom/bidual comparison for a locally finite-projective module in the fixed Poincare datum. It has no adic tensor/cohomology/fibre comparison and its finite-field setting is narrower than the new coefficient calculation. It is not used to infer a general-base statement.

lem-per-adic-lisse-cohomology-calculus vs lem-weil-pbc-locally-constant-tensor: the existing node gives local constancy of the cohomology of a derived tensor over a discrete Noetherian ring when both inputs have locally constant cohomology. It gives neither exact tensor with a degree-zero adic local system and arbitrary constructible K nor the fibre or dual comparisons.

## Review by NX

I checked delivery-errors B--E against the actual statements and sources. The new node introduces its scheme, coefficients, category, L, K and fibres, and explicitly allows locally varying rank and rank zero. Its `proof` and `proof_deps` are empty and it is unsplit. Its exact coefficient category, including the extra uniform-tower/origin conditions, is part of the statement, not a silent consequence attributed to Bhatt--Scholze. The imported item and all maintainer-owned metadata are retained. Its four steps are each below 1,000 characters, so none hides a lemma in a step above the 2,000-character review threshold.

In Step 1 I checked the statements of the new coefficient lemma, `def-per-support-condition`, `def-pod-lisse-l-adic-sheaves`, and `def-weil-pbc-qbar-category`. The calculation and membership conclusion are exactly the first conclusion of the new lemma, and the qbar definition supplies the scheme-domain conditions. The finite-ring constructibility definition is not cited as an adic theorem. Step 2 uses only the two support/perverse definitions and the displayed result of Step 1: tensor sends a zero fibre to zero, inclusion of nonzero-fibre loci persists after closure, and dimensions decrease under closed inclusion by the chain definition. It proves the upper clause rather than citing a new lemma that restates it.

For Step 3 I read the existing Verdier tensor node's full statement. Its smoothness, pure dimension, bounded constructibility and lisse finite-rank hypotheses are precisely those of the item. The coefficient lemma explicitly says that the *linear* dual is lisse and in degree zero; this was missing from the imported argument and is not inferred just from abstract perfectness. The support setting is the bounded constructible Verdier-dual setting in which cosupport is defined. The previous upper argument therefore applies to D_X K and L dual; isomorphism invariance of the cohomology supports then gives exactly the cosupport condition. No unquoted detail of the Verdier node's proof is used. In Step 4 the perverse-definition statement gives the sign of the shift: K belongs to pD^{<=n} iff K[n] belongs to pD^{<=0}, and similarly for >=. I checked the actual signed total-complex differential, including the second-factor summand, and its compatibility with the coefficient-stage construction in `def-weil-derived-pullback-tensor-hom`. The chain isomorphism, followed by the preceding two conclusions, proves every shifted clause.

I checked the new coefficient statement on the empty scheme, L of rank zero, constant rank one, direct sums of the unit of rank r, a sheaf supported at a point, and K shifted by any integer. The expected formulas are respectively empty, zero, identity, r copies, tensor of the supported fibre, and the same shifted cohomology. The degree-zero dual of the zero sheaf is zero. The rank-zero test is what corrected the source's support equality. I also checked that a finite-order coefficient module would need a Tor-flatness hypothesis, so the new lemma stays at the lisse finite-rank rational adic stages and makes no assertion of exact tensor for arbitrary finite-ring local systems.

There are no newly cited proof nodes outside the unit except definitions; the one existing theorem used by the proof, `lem-per-dual-lisse-tensor`, belongs to the same unit. No tool-use exception is needed. Every proof citation has its verbatim statement excerpt in `citations.json`. Every non-elementary comparison used by the proof is either the existing Verdier-tensor theorem or the explicitly stated new coefficient calculation. No compiler, Lake command, direct git command, live-project write or subagent was used.

## Unfinished work

No clause of the item is left as an unargued assertion. The supporting coefficient-calculus node is deliberately statement-only, as required by a one-level split. Its adic comparison and descent proof remains the next stage-1 item; it is not labelled Mathlib, closed, or already proved.
