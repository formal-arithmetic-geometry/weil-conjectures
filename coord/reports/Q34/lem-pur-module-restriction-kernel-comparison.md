## Worker report

The module `Sheaf.CategoryTheory.ModuleRestrictionKernelComparison` states
`CategoryTheory.ModuleRestrictionKernel.moduleRestrictionKernelComparison` and
supplies the canonical constructions and named subclauses of the same node. Every
postponed proof is `sorry`; the functors, kernel comparisons, complex maps, and
localization computation maps have actual data. No new node, dependency repair, or
statement correction is needed. The node JSON changes only in `lean`.

Hypothesis and clause correspondence (names below are in
`CategoryTheory.ModuleRestrictionKernel`, unless qualified):

| Node text | Lean rendering |
| --- | --- |
| Small site, common universe for site and coefficients | `{C : Type u} [SmallCategory C]`, `J : GrothendieckTopology C`, `A : Type u`; the four derived categories have the explicit common localization universe `w`. A Grothendieck topology encodes the covering-sieve presentation of the site's sheaves. |
| Commutative unital ring and constant ring sheaf | `[CommRing A]`; recorded `ConstantLeftModuleInverseImage.Modules J A` unfolds to `ringedSiteModules` of `(constantSheaf J RingCat).obj (RingCat.of A)`. The weak sheafification instance specifies this existing construction; small-site ring sheafification exists. |
| Forgetful functors V and v | Recorded `ConstantLeftModuleInverseImage.V J A` and `LeftModuleDerivedEvaluation.v A`. |
| Monomorphism W to T | `{W T : C} (m : W ⟶ T) [Mono m]`; no open-immersion or terminal-object restriction. |
| Both restriction-kernel functors, with induced action | `S J A m` and `S₀ J m`: objects are categorical kernels of the recorded restriction components; morphisms are their unique kernel lifts. |
| Additive and left exact | `sAdditive`, `s₀Additive`, `sLeftExact`, `s₀LeftExact`; additivity means Mathlib `Functor.Additive`, left exactness means `PreservesFiniteLimits`. |
| Integer complexes and bounded-below derivation | `CochainComplex.Plus`, `DerivedCategory.Plus`, and `rightDerivedFunctorPlus`, with actual integer differentials and the Mathlib localizations. |
| Module category abelian, enough injectives | The category is the recorded `ringedSiteModules` / Mathlib `SheafOfModules`, whose abelian structure is inferred for this small site; `moduleEnoughInjectives` states its enough-injectives clause. Abelian sheaves' enough-injectives instance comes from Mathlib's Grothendieck-sheaf category. |
| Restriction of any injective module sheaf is surjective | First conjunction: `∀ I, Injective I → Function.Surjective ((restriction J A m).app I)`. |
| VI is acyclic for the abelian kernel functor in every positive degree | Second conjunction: all `q : ℕ` with `0 < q`, `IsZero (((S₀ J m).rightDerived q).obj ((V J A).obj I))`. |
| Canonical natural isomorphism c_m on D+ | `comparison` is exactly `rightDerivedFunctorPlusBaseChange` of `kernelIdentity.hom`; the third conjunction is `IsIso (comparison J A m)`. Thus its components are isomorphisms and its naturality is built into the natural transformation. |
| Identity in degree zero | Fourth conjunction is the equality of the two augmentations through `Functor.rightDerivedBaseChange ... 0`. `kernelIdentityObj` is `PreservesKernel.iso`, whose hom is the canonical map obtained from the underlying kernel inclusion. An isomorphism, rather than literal equality of chosen limit objects, expresses the same identity of kernels. |
| Arbitrary injective representatives L and J, arbitrary compatible q | Final universal clause binds `K`, `L`, `N` (the node's abelian representative J), termwise injectivity `_hL`, `_hN`, isomorphisms `eL : QL ≅ K` and `eN : QN ≅ VK`, `q : VL ⟶ N`, its quasi-isomorphism `_hq`, and the exact compatibility equation `_he`. No special resolution is selected. |
| Degreewise short exact restriction-kernel rows | `∀ i : ℤ`, the two displayed `row ... .ShortExact` statements. `row` has the actual kernel inclusion and actual restriction arrow. The forgotten module row is identified with the abelian row by the canonical `kernelIdentityObj`. |
| Morphism of the two rows | For every i the next two equations give the kernel-inclusion square and restriction square, using the component `q.hom.f i` and the induced kernel map. Chain-map compatibility is inherited by applying the existing functors to q. |
| All three maps are quasi-isomorphisms | `QuasiIso (kernelMap ...).hom`, and `QuasiIso (evaluationMap ... T ...).hom`, `QuasiIso (evaluationMap ... W ...).hom`. `kernelMap` and `evaluationMap` are the actual maps induced by q, with the identity of the forgotten complexes inserted. |
| First map is c_m(K) on derived objects | The `forgetCompute ... (S ...)` equation transports along `eL` and `eN` and identifies `Q.map (kernelMap ...)` with the component of the canonical comparison. `compute` is the right-derived unit; `forgetCompute` uses the exact functor's canonical localization factor. |
| Last two maps are the ordinary evaluation comparisons | The last `∀ U, U = T ∨ U = W → ...` equation explicitly uses the recorded `LeftModuleDerivedEvaluation.comparison J A U`. It identifies `Q.map (evaluationMap ...)` with that comparison under the same representative identifications. |
| Independent of L, J, q, and natural in K | A single fixed natural transformation `comparison` is used for every `K`, every pair of representatives and every compatible q; all their induced derived maps satisfy the displayed equalities. Consequently the induced maps do not depend on these choices. |
| No abelian injectivity of VL and no integer flatness of A | There is no such hypothesis. Only L is module-injective and N is abelian-injective. No flatness predicate occurs. |

Dependencies read and used:

- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its documented Grothendieck
  topology / `Sheaf` / section convention is used through the recorded evaluation
  API. `def-weil-size-convention` is a metatheoretic convention, rendered by the
  explicit universes, not an extra Lean object.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` (sheafification of the constant presheaf).
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `def-sp-left-exact-additive`: Mathlib `Functor.Additive`,
  `Limits.PreservesFiniteLimits`, `Functor.rightDerived`, and
  `InjectiveResolution.isoRightDerivedObj` in their recorded modules.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; `def-weil-pbc-bounded-derived-subcategories`:
  `DerivedCategory.Plus` in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `def-sp-enough-injectives` and `def-sp-injective-resolutions`: Mathlib
  `EnoughInjectives`, `Injective`, `InjectiveResolution`, with the extension-property
  and injective-resolution signatures inspected in the recorded modules.
- `lem-pe-left-module-derived-evaluation-forget`:
  `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`; recorded declarations
  `LeftModuleDerivedEvaluation.G`, `G₀`, `v`, `restriction`, `restriction₀`,
  `evaluationIdentity`, `comparison`, and `leftModuleDerivedEvaluationForget`.
  Its `Modules` and `V` come from the imported recorded constant-left-module API.
  No private alternative evaluation or scalar-forgetting functor is defined.
- Stated proof dependencies are imported without `public`: ringed-site Grothendieck
  abelianness, injective monomorphism restriction, module-sheaf scalar-forgetting
  exactness, and module/abelian evaluation comparison. The remaining generic
  homology, injective-representative, five-lemma and right-derived notions are
  Mathlib/upstream interfaces reached through these imports.

Source reading: local `literature/stacks-project/sites-cohomology.tex`,
`lemma-restriction-along-monomorphism-surjective` (093X), lines 1962–2008, and
`lemma-cohomology-modules-abelian-agree` (03FD), lines 1862–1919. Tag 093X proves
restriction surjectivity, not the whole derived kernel comparison. The module's
main docstring reproduces all eight proof steps of the agent-formulated refinement.

Edge cases checked before drafting and again against the signature: identity m
has zero restriction kernels; zero sheaves/zero complexes and the zero ring are
allowed; the empty site is not excluded (there simply are no W,T to instantiate);
there is no terminal-object assumption; arbitrary lower bounds and all integer
cochain degrees are allowed; positive acyclicity includes q=1, while the separate
normalization treats q=0; no flatness or preservation of injectives by V is used.
No statement dispute or node fault was found.

Searches made (all via the authorized `msearch.py` wrapper where applicable):

- LeanFinder: “Forgetting constant module scalars compares the derived kernels of
  restriction along a monomorphism on a small site”: eight hits concerning module
  sheaf limits, scalar forgetting and mono evaluation, no derived kernel comparison.
- Loogle: `"kernelComparison", "rightDerived"`: zero hits.
- Mathlib grep: `restriction.*kernel|kernel.*restriction` in `CategoryTheory`: zero hits.
- LeanSearch: “Forgetting constant ring module coefficients commutes with the bounded
  below derived kernel of restriction along a monomorphism”: eight hits about module
  forgetful functors, preservation of limits/colimits, kernel of a mono, and short
  complex homology preservation; no exact match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id: no match.
  Concept/name searches for restriction/kernel/derived comparison there and in
  `lean/Sheaf` found the already-recorded evaluation API and specialized support
  kernels, but no general small-site restriction-kernel comparison. The specialized
  support functors concern different categories and do not replace this node.
- Inspected Mathlib `kernelComparison`, `PreservesKernel.iso`,
  `NatIso.mapHomologicalComplex`, and the existing bounded-below derived base-change
  construction; these are reused for the new node's canonical maps.

Validation: compiled only through `scompile.py`, successfully in both sandbox and
library-module modes. The first delivery preflight required the three class-instance
proofs to be separate named theorems; `sAdditiveProof`, `s₀AdditiveProof` and
`moduleEnoughInjectivesProof` now carry the postponed proofs, while the instances
refer to those theorems. The delivery dry run recompiles the delivered module. Expected `sorry` diagnostics are the only permitted
warnings. No global build or direct repository/Git mutation was performed.

## Second reading by Q34

I reopened the DAG statement and the complete module after drafting, and performed
this second pass in the worker session (the dispatcher brief prohibits other agents;
the maintainer supplies the independent review). The table above was checked against
both texts, including each hypothesis, all three complex maps, both row squares,
positive acyclicity, the degree-zero augmentation, arbitrary eL/eN/q compatibility,
and the two ordinary evaluation normalizations. I checked the directions of the
localization factors and both representative-transport equations: eL goes QL to K,
eN goes QN to VK, and `_he` says Qq induces those identifications. The construction
of c is fixed before any representative is chosen, which makes the universal
normalization a choice-independence assertion. No mismatch was found and no node
statement was changed. The intermediate elaboration repairs were API spelling and
functor-law simplifications; preflight also required factoring three class-instance
proofs into named theorems. None changed the mathematical statements.
