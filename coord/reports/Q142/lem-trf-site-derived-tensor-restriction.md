## Worker report

Repair of immutable head 086de8825da2 and its L return. I retained the site's balanced
projection formula and repaired the representative/computation interface. The saved packet
was first dry-run unchanged: `OK (dry run): commit e17f8a28a3`; its mechanical success did
not resolve the substantive self-check defects in the return. The sandbox's returned module
was retained as `work/returned.lean` for comparison. The final node was compared field by
field with the current shared main node: only `lean` changes. In particular the original
mathematical `statement` is restored verbatim and `statement_change` is removed.

The module states `CategoryTheory.siteDerivedTensorRestriction`, with `sorry` as its sole
postponed theorem proof. Definitions have actual data. The additional declarations are
helpers for this node's tensor generators, canonical comparison maps and naturality
clauses; they introduce no independent mathematical notion and no new DAG node.

Hypothesis and clause correspondence:

- A site small relative to the module universe is `{C : Type u} [Category.{v} C]`,
  `J : GrothendieckTopology C`, `[EssentiallySmall.{r} C]`. Ring coefficients and module
  sections have universe `r`, independent of `u`, `v` and the derived Hom universe `w`.
  The `HasSheafCompose`, abelian sheafification and locally-bijective infrastructure are
  explicit, as required by the recorded general-site tensor and module-category APIs.
- The ring-sheaf morphism is `φ : R ⟶ S`, with `R S : Sheaf J CommRingCat.{r}`.
  Module categories are the recorded `CategoryTheory.ringedSiteModules.{r}` applied to
  the underlying ring sheaf. The duplicate `RingedSiteModuleSheaves` is removed.
- The two unbounded derived categories are `DerivedCategory` with explicit
  `[HasDerivedCategory.{w} ...]`. The tensor bifunctors are exactly the curry of the
  recorded `SheafOfModules.siteDerivedTensorIndependentCoefficients J R/S`, through
  the transparent abbreviation `siteRestrictionDerivedTensor`. No unrelated `TR`/`TS`
  can be supplied. The old unrecorded `wf_site_derived_tensor_descent` is not imported
  or mentioned anywhere in the final module.
- `E₀`, `hobj`, `hmap`, `[E₀.Additive]`, `E`, `ε`, `hE`, and `hε` bind exactly the
  ordinary and derived change-of-rings data of the recorded
  `derivedChangeOfRingsIndependentCoefficients`: the sectionwise sheafified extension
  on objects and maps, its universal left-derived counit, and invertibility on every
  `IsKFlatIndependentCoefficients` complex. These are the dependency's construction
  data, not an additional flatness or boundedness assumption. `siteExtensionComparison`
  composes the actual counit with `quotientCompQhIso` and
  `mapHomotopyCategoryFactors`, producing `E(QP) ≅ Q(E₀P)`.
- Ordinary restriction is exactly `SheafOfModules.restrictScalars` for the image of `φ`
  under `sheafCompose`. The derived restriction is its `mapDerivedCategory`. Its
  additivity and finite-limit/finite-colimit preservation bind the exact restriction
  data; `mapDerivedCategoryFactors` is used directly, so there is no arbitrary `Res`
  or comparison isomorphism.
- For every `H` and sheaf `N`, the existential `e` has precisely the displayed derived
  tensor/restriction isomorphism type. `siteTensorSingle N` is
  `HomologicalComplex.single ... (ComplexShape.up ℤ) 0`, so `N` is degree zero.
  `ProjectionFormulaFamily ... e` states naturality in each morphism `H ⟶ H'` and
  each sheaf morphism `N ⟶ N'` for this very same `e`.
- `TensorFlatRepresentative P` is just the conjunction of the recorded
  `CochainComplex.IsKFlatIndependentCoefficients` and termwise
  `SheafOfModules.IsFlatOnSite`, with no copied version of either predicate.
  Every integer degree is allowed. `hEP` records that the actual termwise extension
  is also a K-flat flat-term representative, as in the source's computation.
- The existential chain isomorphism `b` goes from the actual total tensor
  `P ⊗ Res(N[0])` to the actual termwise restriction of `(E₀P) ⊗ N[0]`.
  `SiteTensorComplexFunctor` is Mathlib's `map₂HomologicalComplex` of the recorded
  monoidal sheaf tensor, not an unspecified complex or tensor product.
- Both generator formulas are Lean equalities, not docstring descriptions. The first
  quantified clause evaluates `b.hom.f (i+0)` on `siteTotalTmul ... x n` and equates
  it to the total tensor of `siteExtensionTmul ... x 1` with `n`. The second evaluates
  `b.inv.f (i+0)` on the tensor of `siteExtensionTmul ... x s` with `n`, and equates
  it to the tensor of `x` with `s • n`. `siteMonoidalTmul` uses the imported
  `siteSheafTensorTmul` and the recorded `tensorObjIsoSheafification`; `siteTotalTmul`
  then uses the canonical `ιMapBifunctor` summand inclusion. `siteExtensionTmul`
  uses the actual change-of-rings sheafification unit, transporting along `hobj`.
  Its sectionwise convention `s ⊗ x` is the paper's `x ⊗ s`. No identification of
  sheafified sections with sectionwise tensor products is assumed.
- The two derived computations are canonical. `tensorDescentPair` composes the
  complex/homotopy comparison and resolving-class comparison from the recorded
  `site_derived_tensor_descent_independentCoefficients`, with the quotient
  factorizations. `CanonicalOneSidedTensorComparison c` requires naturality in
  every complex in the second variable AND equality to that recorded computation
  when the second factor is K-flat with flat terms. For a K-flat resolution
  `q : Q' ⟶ Q`, this naturality square and the prescribed `Q'` component determine
  the `Q` component uniquely, since `Qq` is invertible. Thus `cR` and `cS` are the
  unique normalized one-sided extensions, not arbitrary existential isomorphisms.
  These equations can be stated using the existing recorded interface, so no
  dependency-module repair is needed.
- The final equality has `(e (DerivedCategory.Q.obj P) N).hom` on the left. Its right
  side is the explicit composite: tensor of restriction's factorization; `cR`;
  `Q.map b.hom`; inverse restriction factorization; restriction of `cS.inv`; and
  restriction of tensor with the inverse change-of-rings counit comparison.
  There are no existential `hsrc`, `htgt`, or separate `eDerived`. Naturality of
  this same `e` along any isomorphism `QP ≅ H` transports this equation to an
  arbitrary representative `P → H`. Because it always computes the fixed `e H N`,
  two choices of representative give the same displayed isomorphism.
- There is no hypothesis that `S` is flat over `R`, no support or boundedness
  restriction on `H`/`P`, and no Tor-amplitude or flatness condition on `N`.

The first four universe parameters in every extraction of the recorded descent theorem
are `u,v,r,w`. The last two parameters are its auxiliary test-category universes, fixed
at `0,0` to extract the exact same witness as the recorded
`siteDerivedTensorIndependentCoefficients` definition. This does not specialize the site,
coefficient or derived-category universes, and no universe equality has been imposed.
All universe names occurring in signatures are declared explicitly; auto-implicits are off.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`, `quotientCompQhIso`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorTmul`; its public tensor interface and upstream
  `SheafOfModules.monoidalCategory`/`tensorObjIsoSheafification`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (the dependency's existing Mathlib match).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients`,
  `siteDerivedTensorIndependentCoefficients`, including their complete comparisons.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `derivedChangeOfRingsIndependentCoefficients`, whose universal counit data are
  bound without replacing the ordinary change-of-rings object or map formulas.
- `Sheaf.Algebra.Homology.KFlat`: `IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategory`, `mapDerivedCategoryFactors`.
  The size-convention dependency is a metatheoretic convention, rendered by the
  explicit independent universes and `EssentiallySmall`, as its record prescribes.

Edge cases checked against the final signature and formulas: empty site; identity
coefficient map; maps to the zero ring sheaf; zero module `N`; zero complex `P`;
nonflat coefficient change; negative degrees and complexes unbounded in both directions;
coefficient universe larger than either site universe; and site object/morphism universes
that differ. The equations use `i+0`, so no degree is excluded. In the identity-map case
both balanced formulas reduce to the ordinary tensor identity. In the zero-module case
the generators vanish and both sides are zero. Local generation, not surjectivity of
sectionwise sheafification, is what makes the formulas characterize the maps.

Searches retained from the saved investigation and repeated in the repair:

- `msearch.py ... leanfinder "Derived tensor on a ringed site with scalar restriction
  balanced chain isomorphism and canonical K-flat representative comparisons"`: eight
  hits about ordinary module flat tensor and Tor; none is this general-site theorem.
- `msearch.py ... loogle "siteDerivedTensorIndependentCoefficients,
  siteSheafTensorTmul"`: zero hits; the project names are not in Mathlib's index.
- Saved LeanSearch queries about derived tensor with restriction of scalars returned
  ordinary `ModuleCat` extension/restriction and flatness only; the exact search output
  is retained in the node's unchanged `mathlib_searches`.
- `rg` in the upstream `WeilConjectures` and shared `lean/Sheaf` trees: no existing
  derived general-site scalar-restriction formula. The balanced-contraction modules
  found concern topological spaces and the ordinary tensor and do not state this
  unbounded arbitrary-site theorem. The localized-site tensor theorem concerns a
  different operation (restriction to a slice site).
- The complete current recorded interfaces were read locally, and `scompile.py --source`
  was also used for the live descent, change-of-rings, and ringed-module modules.
  A probe confirmed the independent-universe interfaces and that the imported
  `siteSheafTensorTmul` transports through `tensorObjIsoSheafification` as used here.

No mathematical statement correction, `STATEMENT-DISPUTED`, new node, or dependency
module is part of this repair. The two citers, `lem-trf-ordinary-kunneth` and
`lem-sfb-local-model-tor-bound-descent`, continue to use the original natural formula
and representative clause. Neither citer is edited.

## Second reading by Q142

I reread the original node's complete statement, its seven proof steps, blueprint
Step 2, and the final Lean module after the rewrite. I checked the return as follows.

H3(i): previously the only conditions on `chainIso` were identities automatic for every
isomorphism. The final two quantified element equations now constrain both its forward
and inverse maps on all local pure tensor generators, in every integer degree. I traced
`siteTotalTmul` through `ιMapBifunctor`, `siteMonoidalTmul`, `tensorObjIsoSheafification`
and the imported `siteSheafTensorTmul`; the extension element also goes through the
actual module-sheafification unit. These are genuine local generators in the stated
objects, not elements of a falsely identified sectionwise tensor product.

H3(ii): the conclusion quantifies one `e`. `ProjectionFormulaFamily ... e` and the last
representative equality refer to that identical binder; the former existential
`eDerived` is gone. I checked both naturality equations against the source and target
of `e`, including the degree-zero single functor on sheaf morphisms. Their naturality
also gives the prescribed arbitrary-lift/identity cases for `QP ≅ H`.

H3(iii): I traced the final equality from left to right. Each adjacent morphism has the
correct derived object as source and target. The source comparison is restriction's
`mapDerivedCategoryFactors` followed by `cR`. The target comparison is restriction's
factorization, `cS`, and `siteExtensionComparison`, whose middle arrow is the actual
universal derived-change-of-rings counit. I checked that `cR`/`cS` cannot absorb the
claimed equality by being arbitrary: naturality at a K-flat resolution plus their
normalization at its source uniquely determines each component. Normalization is the
recorded descent comparison itself, not an independently quantified isomorphism.

H4/H13: all module categories use `ringedSiteModules`; all K-flat occurrences use
`IsKFlatIndependentCoefficients`; all derived tensors use the recorded independent
coefficient descent. The old `wf_...` import is absent. I checked the independent
`u,v,r,w` parameters and the role of the two auxiliary `0` universes separately; they
do not impose a site/coefficients equality. The exact existing comparison interface
suffices, so I did not invent a duplicate dependency theorem.

H7: I compared the copied JSON with current main: the mathematical `statement` is
identical, `statement_change` is absent, and no dependency/proof field changes. There
is no section presenting an implementation repair as a mathematical correction.

H8: I checked every declaration, including the helper abbreviations and canonical-map
definitions, has a source-bearing blueprint docstring. The main theorem carries the
seven-step natural-language proof. The docstrings' generator and canonical-comparison
claims are now actual constraints in the Lean statement.

H11: this reading found and repaired the unrelated representative isomorphism,
missing generator formulas, arbitrary comparison isomorphisms, old predicate/category
copies, and spurious statement correction. I then checked every hypothesis and every
clause in the correspondence above, particularly arbitrary degree-zero `N`, no
flatness of `S`, unbounded complexes, and representative independence. Only the named
main theorem retains `sorry`; helper definitions contain concrete data and compositions.

Validation: the final delivered module compiled cleanly through `scompile.py` in both
its sandbox and library-name invocations (48.8 s and 58.6 s), within the required
60-second per-file limit. The preceding repaired version also compiled cleanly twice
(37.5 s and 40.4 s); the only intervening Lean edit removed an unused helper definition.
The packet self-check verified the declaration list, verbatim signature, source/blueprint
docstrings, 100-character lines, sole `sorry`, and the lean-only node delta.
