## Worker report

The module states `AlgebraicGeometry.Etale.dg_etale_injective_finite_cech_rows`, with
one postponed theorem and four concrete helpers belonging to its Čech construction.
Its source is Stacks Tags 02FU, 08FI, 0136 and 0137, and paragraph 2 of the current
`main-20261015` blueprint proof of `thm-dg-finite-type-constructibility`. I read the
covering-resolution insertion proof, the localized module-site definition and exact
extension-by-zero adjunction, and the injective splitting and product lemmas.
There is no statement correction, new definition node, or dependency replacement.

Clause-by-clause correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`. The small étale site is
  `X.smallEtaleTopology`, with its existing scheme-theoretic pullback functor.
- An arbitrary commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]`.
  `J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` is the project's authorized
  fixed-coefficient encoding of a module over the constant ring sheaf. This is the
  second coexisting encoding explicitly authorized by `def-weil-pbc-etale-sheaves`
  (decision of L, 2026-10-11), used by the recorded inverse/direct image functors and
  the six-functor chapter. The general ringed-site encoding remains the recorded
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules` over
  `(CategoryTheory.constantSheaf X.smallEtaleTopology RingCat).obj (RingCat.of A)`.
  An action of the constant sheaf is equivalently a compatible action of A on sections:
  locally constant scalars act locally, and these local actions glue uniquely. The
  statement introduces no alternative category, action or equivalence choice.
- Injectivity is exactly the recorded `[CategoryTheory.Injective J]`.
- The nonnegative number of opens is `(r : ℕ)`; `U : Fin r → X.Opens` orders them,
  and `hU : iSup U = ⊤` is precisely the covering condition. There is no positivity
  hypothesis on r and no geometric or coefficient finiteness hypothesis.
- A nonempty subset of cardinality p+1 is represented uniquely by its increasing
  enumeration `t : Fin (p + 1) ↪o Fin r`. The already existing
  `AlgebraicGeometry.alternatingCechIntersection U t = ⨅ k, U (t k)` is U_I.
- `finiteCechOpenTerm A J V` is the recorded `Etale.lowerStar` of the existing
  `Etale.openImmersionRestriction` at V. The latter is the existing sectionwise model
  of inverse image, canonically isomorphic to the recorded `Etale.upperStar` via
  `Etale.upperStarIsoOpenImmersionRestriction` (and its general étale version
  `Etale.upperStarIsoLocalizationRestriction`). Thus the term is exactly u_*(J|_V).
- `T p`, its projections `π p t`, and
  `Nonempty (IsLimit (Fan.mk (T p) (π p)))` present the product of these summands.
  There are finitely many increasing tuples, so this product is canonically the
  stated finite direct sum in the abelian category. The universal property and the
  component equations determine the complex up to its unique coordinate isomorphism;
  they do not permit an unspecified replacement differential.
- `finiteCechTestObject W V` is W ×_X V viewed over X, using exactly the existing
  base-change and localization functors, with actual data. Its projection is
  `finiteCechTestProjection`; an open inclusion induces `finiteCechTestInclusion`,
  constructed by the pullback universal property, preserving both projections.
- Deletion of position a is `(Fin.succAboveOrderEmb a).trans t`. The differential
  equation is quantified over every degree, target tuple, étale test object W and
  section s. It is exactly the sum of `(-1 : ℤ)^a.val` times the indicated component
  restricted by `J.obj.map (finiteCechTestInclusion W ...).op`.
  `alternatingCechIntersection_face_le` supplies the existing face inclusion.
- The equation for `ε` gives every singleton projection as restriction along
  `finiteCechTestProjection`; thus ε is the canonical augmentation, not an arbitrary map.
  `hdd` states square zero, and the existential `hε` states ε followed by d0 is zero.
- `∀ p, r ≤ p → IsZero (T p)` gives all terms past the finite range; natural-degree
  cochain complexes have no negative terms. This is the stated finite cochain row.
- `Mono ε` is exactness at J. `(ShortComplex.mk ε (d 0) hε).Exact` is exactness at C0.
  `(CochainComplex.of T d hdd).ExactAt (p + 1)` gives exactness at every subsequent
  term, including the terminal term whose target is zero.
- `∀ p, IsSplitMono (kernel.ι (d p))` means that each cycle inclusion has a retraction.
  At degree zero exactness and monicity identify this kernel with J, so this also
  splits the augmentation. These are the cycle short exact sequence splittings in
  the node; it does not demand that an arbitrary three-term segment itself split.
- `∀ p, Injective (T p)` is the injectivity of every term, including zero terms.
  `r = 0 → IsZero J` explicitly records the specified empty-cover endpoint.

Dependency declarations read and used (including module/docstrings and full signatures):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`,
  and its jointly-surjective-cover characterization.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  whose body is exactly Mathlib `SheafOfModules`; the module is imported.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the constant presheaf; used to identify the coefficient interpretation.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  its factors field is the extension property across every monomorphism.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`; imported transitively
  by the existing open-immersion module.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionRestriction`, `Etale.upperStarIsoOpenImmersionRestriction`,
  `Etale.upperStarIsoLocalizationRestriction` and its restriction adjunction.
- `Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`:
  `AlgebraicGeometry.alternatingCechIntersection` and
  `AlgebraicGeometry.alternatingCechIntersection_face_le`. Its owning landed node
  `def-sc-alternating-cech-total-complex` is added to stmt_deps, avoiding a second
  definition of ordered intersections.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the existing fixed-coefficient
  convention in `def-weil-pbc-etale-sheaves`. This landed node and the existing
  inverse-image/restriction comparison node are also added to stmt_deps.
  The current source was read through `scompile.py --source` because this source
  module is absent from the older local upstream checkout.

Edge cases checked: r=0 makes iSup U bottom, so the covering condition forces X empty;
all indexing types are empty and the theorem explicitly gives J=0. For r=1 the cover
is X itself, the degree-zero augmentation is an isomorphism, and all later terms vanish.
Empty intersections contribute the zero sheaf. Repeated or empty members of a nonempty
cover are allowed. The zero sheaf and zero coefficient ring cause no excluded case.
The top-degree kernel inclusion is the identity up to its kernel isomorphism, and
out-of-range zero terms satisfy both exactness and split inclusion. Coefficients and
section carriers use u+1, matching the existing étale-site size convention without
forcing its object universe u+1 equal to its morphism universe u.

Searches made:

- `msearch.py`, LeanSearch: "injective sheaf modules finite open covering alternating
  Cech resolution split exact". Eight hits: module-sheaf constructor injectivity,
  `ShortComplex.ShortExact.splittingOfInjective`, injective resolutions and stalk tests.
  None states the finite ordered étale Čech row theorem.
- `msearch.py`, Loogle: `CategoryTheory.Injective, "split"`. Two hits:
  `ShortComplex.ShortExact.splittingOfInjective` and
  `CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective`. These require
  exactness/quasi-isomorphism as input and do not construct this row.
- `msearch.py`, LeanFinder: "finite ordered Cech resolution injective etale module
  sheaves split exact". Eight hits, including module sheafification local injectivity,
  injective resolution terms, the local-injectivity test for sheaf morphisms, and
  `CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective`; no matching row theorem.
- `msearch.py`, Mathlib grep `Cech|cech|Čech` in `CategoryTheory/Sites`: six hits,
  the general site Čech construction and an H1 TODO. Reading the construction shows
  all-tuples site Čech cochains, not this finite increasing-subset sheaf resolution.
- `rg` in `WeilConjectures/SixFunctors/Etale` for `Cech|cech|Čech`: the finite-type
  constructibility source mentions the proof but has no declaration stating this row.
  Searches for the item's id and for `finiteOrderedCech`, `finiteCechOpenTerm`, and
  the main declaration found no existing declaration for the item.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for the same notions found the existing
  ordered intersection and the ringed-space alternating Čech construction. I reused
  its intersection and face inclusion; the ringed-space theorem uses O_X-modules,
  not constant-coefficient étale module sheaves.
- DAG searches for finite ordered Čech/injective rows and constant-module encodings
  confirmed this item is the owning statement; no separate construction node is needed
  for the four helpers, which are part of this node's explicitly specified row.

The retained earlier attempt had no report/node copy. Its arbitrary differential and
augmentation did not constrain the Čech maps, and its `ShortComplex.Splitting` clauses
incorrectly imposed split short exactness on each three-term segment. These were
replaced by the actual component formulas, exactness, and retractions of kernel
inclusions. No mathematical fault or disputed source statement remains.

Validation: the final module was compiled individually through `scompile.py`, both
sandbox and library-path checks, with no errors or warnings. Every variable/universe
is explicitly bound (`autoImplicit false`). Definitions have concrete data; the only
theorem proof is `sorry`, with the full proof plan in its docstring. The first
`deliver2.py --no-push` finished successfully: preflight and all file compiles passed
(commit 64fcd0a0a0; nothing pushed).

## Second reading by Q11

This reading replaces the delivered self-check. The delivered self-check stated that no independent
reading had been made, which is fault H11. The maintainer's independent second reader
(cc review service, run 2) made this reading at head 02aa144f7aa6 with the node, the Stacks
place and the module open. The Lean was not changed.

Node clauses and the Lean that renders them:

- Scheme X, commutative ring A, the small étale site: `(X : Scheme.{u})`,
  `(A : Type (u + 1)) [CommRing A]`, `X.smallEtaleTopology` (the recorded declarations of
  def-pc-scheme and def-weil-pbc-etale-site). Correct.
- Universe in which module sheaves are abelian; A_X-module sheaves: these are
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`. This is the second coexisting encoding
  authorized in the lean.note of def-weil-pbc-etale-sheaves (decision of L, 2026-10-11,
  Λ : Type (u+1)). A probe confirmed that `Abelian` resolves for this category. The convention
  is authorized, so this is not a silent universe restriction. Correct.
- r ≥ 0 and the open cover U_1..U_r: `(r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)`. For
  r = 0, `iSup U = ⊥`, so X is empty, exactly as the node says. Correct.
- U_I for nonempty I, and u_I: I is its increasing enumeration `t : Fin (p+1) ↪o Fin r`, and
  U_I is the landed `alternatingCechIntersection U t = ⨅ k, U (t k)`
  (def-sc-alternating-cech-total-complex). Correct.
- Injective J: `[Injective J]`, which is CategoryTheory.Injective of def-sp-injective-resolutions.
  Correct.
- C^p(J) = ⊕_{|I|=p+1} u_{I,*}(J|_{U_I}): `T p` with projections `π p t` onto
  `finiteCechOpenTerm A J (U_t) = lowerStar (openImmersionRestriction J)`, and
  `IsLimit (Fan.mk (T p) (π p))`. The finite product is the biproduct. `lowerStar` is the
  recorded direct image. `openImmersionRestriction` is canonically isomorphic to the recorded
  `upperStar` through `upperStarIsoOpenImmersionRestriction`, the companion of the recorded
  lem-weil-pbc-etale-inverse-image-restriction declaration in the same module. A probe proved by
  `rfl` that the sections of the term over W are `J(W ×_X U_t)`. Correct.
- Other terms are zero: `∀ p, r ≤ p → IsZero (T p)`. The fan over an empty index type agrees.
  Correct.
- The differential (d^p s)_I = Σ_a (-1)^a s_{I∖{i_a}}|_{U_I}: the component equation for every
  p, t, W and s. Deleting position a is `(Fin.succAboveOrderEmb a).trans t`. The restriction is
  `J.obj.map (finiteCechTestInclusion W (face_le ...)).op`, and the sign is `(-1 : ℤ)^a.val`.
  Correct, and d is determined by the limit.
- The augmentation by restrictions: the ε component equation is restriction along
  `finiteCechTestProjection`. Correct.
- The augmented sequence is exact: `Mono ε`, then `(ShortComplex.mk ε (d 0) _).Exact`, then
  `ExactAt (p+1)` of `CochainComplex.of T d hdd`. This includes surjectivity onto C^{r-1},
  since the next term is zero. Correct.
- Each cycle inclusion has a retraction: `∀ p, IsSplitMono (kernel.ι (d p))`. At p = 0 the kernel
  is J, through exactness and mono. Three-term segments are not required to split. Correct.
- Every C^p(J) is injective: `∀ p, Injective (T p)`. For r = 0, J = 0: `r = 0 → IsZero J`.
  Correct.
- The Lean adds no affineness, separatedness, finite-type or finiteness hypothesis.

Edge cases checked: r = 0; r = 1, where the augmentation is an isomorphism; empty and repeated U_i;
empty U_I, where the term is zero; degrees p ≥ r; the zero ring A.

Searches: the worker's three kinds of search, and rg for `Cech` and `splittingOfInjective` in
Mathlib and the side lean tree. None found an existing statement of this row.

Mismatches: none in the Lean or the node record. The node's `lean.statement` is verbatim the
file signature. The three added stmt_deps are landed nodes whose declarations the module uses,
and adding them creates no cycle.

The module was compiled again with tools/nt_compile.py: clean. `#print axioms` gives only
sorryAx and the standard axioms.
