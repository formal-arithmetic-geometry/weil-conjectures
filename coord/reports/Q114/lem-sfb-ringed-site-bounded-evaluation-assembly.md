## Worker report

The delivery states `CategoryTheory.RingedSiteBoundedEvaluation.assembly` in
`Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly`. Its only postponed proof
is `assembly`. All other declarations are concrete specializations or predicates on
existing constructions. No source statement correction or dependency repair is proposed.

Hypothesis and clause correspondence:

- A small ringed site with commutative coefficients is `C : Type u`, `[Category.{v} C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{max u v w}`. The universes
  `u`, `v`, `w` are independent; the common coefficient/module universe contains both
  site universes, as required by `def-weil-size-convention`. It does not impose equality
  of object and morphism universes. `Modules` is the recorded `ringedSiteModules` alias
  of Mathlib `SheafOfModules`, not another category.
- The complexes are unrestricted `E F : CochainComplex (Modules R) ℤ`.
  The integers `a b` and `hbounded : ∀ i, i < a ∨ b < i → IsZero (E.X i)`
  express exactly the termwise support condition. No inequality `a ≤ b` is imposed.
- `θ i M` has source `M ⊗ homObj (E.X i) (𝟙_ _)` and target `homObj (E.X i) M`.
  `IsModuleEvaluation` pins it on every object and every slice to
  `phi(x) • restriction(y)`. `pureTensor` uses the actual sheafification unit followed
  by the inverse of `tensorObjIsoSheafification`. Thus the formula concerns actual
  local pure tensors and does not assume global tensor-section generation.
  The theorem first constructs the canonically characterized theta family, then
  assumes `∀ i M, IsIso (θ i M)` in the implication. This represents the stated
  canonical-map hypothesis without postulating arbitrary maps or replacing the
  comparison with a bare unspecified isomorphism.
- `unitComplex R` specializes Mathlib `HomologicalComplex.single` at integer
  degree zero and the coefficient tensor unit: this is exactly R[0].
  `dual R E` is exactly the recorded `homComplex E (unitComplex R)`.
  `total R E F` specializes the recorded `CochainComplex.mapBifunctor`
  at F, the ordinary dual, and the actual curried tensor functor.
  Its small colimits and finite biproducts come from existing category instances.
- `ε : total R E F ≅ homComplex E F` includes both the asserted chain map
  `ε.hom` and its inverse chain map `ε.inv`. The first formula after the dual
  projections specifies evaluation on all pure tensors and every slice when
  `r+q=0`. The next formula makes the whole component morphism zero when
  `r+q≠0`. Thus the hom is uniquely characterized by the stated sign-free formula;
  it is not an arbitrary isomorphism.
- `δ i` is the ordinary dual projection in degree `-i`, explicitly pinned by
  `(δ i).hom = dualProjection R E (-i) i ...`. It is not an unspecified dual identification.
- The finite families are indexed by `↥(Finset.Icc a b)`. `sourceFamily` is
  `F.X (i+n) ⊗ homObj (E.X i) (𝟙_ _)` and `targetFamily` is
  `homObj (E.X i) (F.X (i+n))`. The node's `n+i` is written `i+n`, the indexing
  convention of the recorded Hom projection; integer addition is commutative.
  The source isomorphism `s` is pinned on every biproduct inclusion by tensoring
  `(δ i).inv` and using the inclusion at `(i+n,-i)`. The target isomorphism `t`
  is pinned on every projection by `homComplexπ`. These equations specify the
  canonical identifications, including empty support. The displayed equation
  `s.hom ≫ ε.hom.f n ≫ t.hom = biproduct.map (fun i ↦ θ i.val (F.X (i.val+n)))`
  is the required finite diagonal matrix equality.
- The differential clause compares `inclusion ≫ total.d ≫ ε ≫ homComplexπ`
  with the projected `d_F f - (p+q).negOnePow • f d_E`, for every `p,q,r`.
  The tensor side uses the recorded tensor differential and the actual ordinary
  Hom dual differential. Expanding these is exactly
  `d_F y tensor phi + (-1)^(p+q+1) y tensor (phi d_E)`.
  This is also explained, with both support degrees, in proof step 5 of the docstring.
- `∀ n, IsIso (ε.hom.f n)` records every degreewise isomorphism, and the final
  conjunction records both componentwise inverse equations. Since `ε.inv` is
  a complex morphism, these are the asserted degreewise inverses forming a chain map.
- There is no boundedness hypothesis on F, K-flatness, or finite-free retract datum.

Dependency declarations used:

- `def-weil-size-convention`: explicit independent universes, no declaration.
- `def-pur-sheaf-tensor-product`: public import
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, using the
  recorded `SheafOfModules.cochainModulesMonoidal` and its additive structure.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap` (exported through HomComplexComponents).
- `def-pur-hom-complex`: `WeilConjectures.Algebra.Homology.HomComplex`,
  `CategoryTheory.homComplex`, with the actual projections `homComplexπ` from
  `WeilConjectures.Algebra.Homology.HomComplexComponents`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor`, `CochainComplex.ιMapBifunctor`.
- `def-weil-presheaf-modules-sheafification`: Mathlib
  `PresheafOfModules.sheafificationAdjunction` at the identity coefficient map.
- `def-weil-sheaf-of-modules-category`: public import
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- The proof dependency `lem-sfb-ringed-site-bounded-dual-components` has no recorded
  module in the read repository; its proof is described in step 1 of the docstring,
  and its actual projection construction is the existing Hom-complex API. There is
  no fabricated import or added assumption for that unstated proof dependency.

Edge cases checked before writing: `a>b` gives an empty interval and E=0 in all
integer degrees; the source and target finite biproducts are zero and all maps
are the unique zero-object maps. A one-degree E has a single diagonal block.
Negative degrees use `Int.negOnePow`, so signs have their integer-degree meaning.
For E with two adjacent nonzero terms, the two differential components are at
`r=-q` and `r=-q-1`, with respective coefficients 1 and `(-1)^(p+q+1)`.
F can be unbounded in both directions, and the zero coefficient sheaf is allowed.

Searches before writing:

- msearch.py leanfinder: "A bounded complex of sheaves with invertible tensor dual Hom
  comparisons has an invertible tensor Hom evaluation chain map". Eight hits:
  condensed internal projectivity and `HomologicalComplex.rightUnitor` variants;
  none states the general ringed-site finite-support evaluation calculation.
- msearch.py loogle: "CochainComplex, CategoryTheory.MonoidalClosed". Zero hits.
- msearch.py grep: "evaluation.*homComplex|homComplex.*evaluation|tensor.*Hom.*Iso".
  Twenty-five hits, including module and monoidal tensor formulas, no exact match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for bounded evaluation, tensor-Hom
  comparisons, and the node id. The node id has no upstream declaration.
  `WeilConjectures.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly` is the
  closest theorem: `AlgebraicGeometry.boundedOrdinaryEvaluation_degree` requires
  a Scheme and an open U, assumes an already constructed evaluation chain map,
  and only concludes its degreewise invertibility. It is not this general-site
  construction with its diagonal identifications and sign formula. Its data
  module was read to check the intended order and normalization of evaluation.
- The upstream declaration-name index was checked for collisions; the namespace
  `CategoryTheory.RingedSiteBoundedEvaluation` is new. All fundamental objects are
  imported from their owning declarations, and no alternative tensor or Hom is made.
  The general-site `ringedSiteOrdinaryEvaluation` in RingedSiteDualityMaps was also
  inspected: it constructs the ordinary map, but does not assert this finite-support
  assembly. That module is excluded by `coord/route-pivot-dropped.txt`; preflight
  explicitly rejects importing it. The final module therefore uses only the item's
  original recorded tensor and Hom constructions. The evaluation formula is a
  clause of this theorem, not another definition of a canonical evaluation map.


Source reading: Stacks `sites-cohomology.tex`, lines 13048–13133 (08JJ), and
8571–8601 (0A8X), alongside the node's eight proof steps. The former reduces
ordinary evaluation to the module comparisons; the latter fixes the Hom sign.
No statement fault or disputed mathematical claim was found.

## Second reading by Q114

This was a separate pass by the same dispatched worker: the dispatcher explicitly
prohibits starting another agent, and the maintainer performs the independent review.
I reopened the node and module and matched the support hypothesis, the full
universal termwise comparison hypothesis, the O and D definitions, both homogeneous
support cases, both canonical finite-sum identifications, their diagonal matrix,
the differential equation, and both inverse equations as detailed above.
The existential theta is uniquely fixed on all local pure tensors, so its subsequent
invertibility implication is the same hypothesis about the canonical map, not
an arbitrary family of isomorphisms. The finite sums use the same interval on both
sides, including the empty interval. The source identification has direction sum
to total, which is why its formula uses the inverse dual projection. The target
identification has direction Hom to sum, with the actual Hom projections.
The coefficient and module universe is the maximum containing the separate site
universes; no equality between site object and Hom universes was introduced.

The second pass checked every local tensor restriction, both support cases, the
projection normalization of the ordinary dual, and both biproduct universal-property
normalizations. Preflight ruled out importing the route-pivot-dropped duality module;
the final statement characterizes the comparison by its explicit formula instead.
The only changes to the node are its Lean record. There are no new nodes,
dependency modules, statement corrections, or added hypotheses. No maintenance
repair note exists for this item.

Final validation: scompile.py compiled this exact module in sandbox (15.5 s) and
library (20.0 s) modes, with no errors or warnings.
