## Worker report

The module `Sheaf.Paper.FlatScalarDirectImageLimitCoherence` states
`CategoryTheory.FlatScalarLimitCoherence.flatScalarDirectImageLimitCoherence` with
one `sorry`. It supplies only transparent specializations of existing module categories,
restriction of scalars and termwise postcomposition as helpers. The ordinary and derived
maps are specified by their normalization equations, not merely by their endpoints.
The source read was Stacks `sites-cohomology.tex`, label
`lemma-Rf-commutes-with-Rlim` (0A07), its first proof and the immediately preceding
derived-limit section (0940). The scalar-coherence refinement follows all eight proof
steps of the DAG node; the module docstring records that argument.

Hypothesis and clause correspondence:

- Small sites and a geometric morphism: `C D : Type u`, `[SmallCategory C]`,
  `[SmallCategory D]`, topologies `K H`, and `x : FlatRingedDiagramInput K H`.
  Its `R.morphism` and `S.morphism` are the recorded `RingedToposMorphism`s,
  with the same underlying inverse, direct and geometric adjunction.
- Four commutative ring sheaves and two flat coefficient maps: `x.RU`, `x.SU`,
  `x.RV`, `x.SV : Sheaf ... CommRingCat`, `x.aU`, `x.aV`, `x.flatU`, `x.flatV`.
  Flatness is exactly `SheafOfModules.IsFlatOnSite` of the restricted coefficient
  unit, using the dependency's exact sheaf tensor predicate.
- The specified inverse-image ring isomorphisms and their compatibility are
  `x.R.inverse.ringUnderlying`, `x.S.inverse.ringUnderlying`, and `x.coherent`.
  The module adjunctions in `x.R` and `x.S` are chosen induced adjunctions, fixed
  by their `transpose` equations, not extra exactness hypotheses.
- Countable products are exact in each of the four categories: the theorem's four
  explicit `HasExactLimitsOfShape (Discrete ℕ)` binders. Their placement on the
  theorem itself ensures these hypotheses are retained in its elaborated type.
- Module categories are the recorded `ringedSiteModules`/Mathlib `SheafOfModules`,
  transparently named `RU`, `SU`, `RV`, `SV`; derived categories are Mathlib
  `DerivedCategory.{w}` with its eight explicit `HasDerivedCategory` instances.
  These instances choose localizations at quasi-isomorphisms, not new mathematical
  properties. `CochainComplex ... ℤ` covers unbounded complexes.
- `F_Z` and its termwise tower functor: `x.R.morphism.modules`,
  `x.S.morphism.modules`, and the helpers `FRt`, `FSt`, which are exactly
  `Functor.whiskeringRight ℕᵒᵖ ...` applied to those functors.
- Derived direct images: `FR`, `FS`, `FTR`, `FTS`, with units `ηFR`, `ηFS`,
  `ηFTR`, `ηFTS`. Each `_universal...` is the existing `IsRightDerivedFunctor`
  predicate and each `_computes...` says its unit is invertible on K-injectives.
  This is precisely the dependency's choice-independent derived model interface.
- `L_{U,R}`, `L_{U,S}`, `L_{V,R}`, `L_{V,S}`: `LUR`, `LUS`, `LVR`, `LVS`,
  with units from ordinary degreewise `lim`, universal and invertible on
  K-injective tower complexes. These are the recorded total derived limits.
- Actual scalar restriction: helpers `rU`, `rV` are the Mathlib sheaf restriction
  functors of the given ring maps; `rUt`, `rVt` are their exact postcomposition on
  towers. `rUD`, `rVD`, `rtUD`, `rtVD` are their chosen localized functors, with
  `qrUD`, `qrVD`, `qrtUD`, `qrtVD` fixing their localization factors on complexes.
- Canonical ordinary scalar/direct-image identity: `d0`, with `_ordinaryD`
  exactly the underlying-sheaf direct-image normalization of the recorded
  `OrdinaryComparisonsNormalized` predicate at a single index. Its tower version
  is literally `(Functor.whiskeringRight ℕᵒᵖ ...).mapIso d0`.
- The specified derived maps `d`, `d^Tow`: `d`, `dt`, with `_normalizedD` and
  `_normalizedDt`, the dependency's right-derived-unit equation. On K-injectives
  the units are invertible, so these fix the maps to localization of the ordinary
  identity on that same complex, with all tower arrows retained.
- Canonical ordinary scalar/limit maps: `betaU`, `betaV`, with
  `_ordinaryBetaU`, `_ordinaryBetaV` setting their components to `limit.post`.
  Thus their nth projections are the restricted original projections.
- Resolution-normalized scalar/limit maps: `lambdaU`, `lambdaV`. Their
  `_normalizedLambdaU/V` equations express localization of precisely those beta
  maps through the derived-limit units and the scalar-localization factors.
  On a K-injective tower and its K-injective restriction this is the identity-target-
  resolution case of `exactProductFunctorStrictLimit`; naturality along a resolution
  gives its arbitrary-resolution formula. Conversely that formula determines these
  equations. The chosen localized scalar functors may be transported along their q
  factors; no independent comparison automorphism remains.
- The two `c^Z` are `cR`, `cS`. The ordinary `eR`, `eS` components are fixed to
  `limit.post`, so they are the actual ordinary direct-image/limit comparisons.
  `_normalizedCR/CS` are verbatim the common-composite derived-unit normalization
  in `ringedTowerPushforwardLimitComparison`, with the present coefficient labels.
- The displayed equality is the first conjunct, for every `M` in
  `DerivedCategory (ℕᵒᵖ ⥤ SU x)`. Lean's `≫` lists the maps in application order:
  `rVD.map (cS.hom.app M) ≫ lambdaV.hom.app (FTS.obj M) ≫ LVR.map (dt.hom.app M)`
  equals `d.hom.app (LUS.obj M) ≫ FR.map (lambdaU.hom.app M) ≫ cR.hom.app (rtUD.obj M)`.
  These are exactly the two sides in the node, with the same direction and endpoints.
- Naturality in actual derived strict-tower morphisms is the second conjunct,
  quantified over `f : M ⟶ N` in that derived category, not a morphism of its
  levelwise evaluations. Thus the equality identifies the specified maps, not
  merely two isomorphic pairs of endpoints.
- The last conjunct starts with an actual K-injective tower complex `I` and asserts
  that the actual termwise-restricted complex is K-injective. The all-complexes
  `_normalizedD`, `_normalizedDt`, `_normalizedLambdaU/V`, and `_normalizedCR/CS`
  equations already state the computation of the specified maps using the ordinary
  `d0`, `beta`, and `e` on these very complexes. On a K-injective source all relevant
  source units are invertible (ordinary limit preserves K-injectives as in proof
  step 2). Thus these equations give exactly the common-model computation in the
  node's final clause, with no change of source representative. No extra target-
  resolution formula is added to the conclusion.
- No boundedness, completeness, coefficient-finiteness, or etale-origin predicates
  occur in the theorem.

Dependency declarations and interfaces read:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, with `CategoryTheory.exactFunctor`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (full definition read).
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`:
  `CategoryTheory.FlatRingedDiagramInput.flatRingedDiagramRestriction`, together
  with its `DerivedRestrictionComparison` and the normalization predicates.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit`, especially its projection-
  normalized ordinary beta and arbitrary K-injective-resolution normalization.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`, including the explicit
  ordinary `limit.post` equation and its all-complexes derived-unit equation.
- The already landed definition `def-weil-pbc-flat-ringed-diagram-input` was added
  to `stmt_deps` because the statement directly uses its data. Its existing module
  `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs` supplies
  `CategoryTheory.FlatRingedDiagramInput` and `FlatRingedModuleImage`; their full
  definitions were read. No dependency record was changed and no new node was needed.

Proof-only imports also cover the recorded diagram-site realization, K-injective
resolution existence, target-limit acyclicity, right-adjoint preservation of
K-injectives, the Mathlib K-injective Hom comparison, and levelwise abelian towers.

Edge cases checked: zero complexes; zero ring sheaves; empty presented sites;
identity coefficient maps and identity geometric morphisms; nonconstant tower
transition maps; arbitrary positive/negative cochain degrees; arbitrary coefficient
universe `u` and chosen localization universe `w`. The tower is inherently nonempty.
Positive indexing is reindexed by `n ↦ n+1`, with no lost first level. The input's
same-universe diagram abbreviations cannot take native `ℕ` for arbitrary `u`; the
four transparent tower helpers use Mathlib's universe-polymorphic postcomposition
instead, preserving exactly the existing functors. No universe equality is imposed.

Searches actually run with the prescribed wrapper:

- LeanFinder: `Flat scalar restriction commutes with the normalized derived direct
  image strict inverse limit comparison`: 8 hits, concerning ordinary module flatness,
  scalar restriction, and unrelated flat functors; no derived coherence match.
- Loogle: `Functor.IsRightDerivedFunctor, limit.post`: 0 hits; Loogle did not know the
  identifier `Functor.IsRightDerivedFunctor`, so this result is not a completeness claim.
- Grep: `scalar.*[Ll]imit|[Ll]imit.*scalar` in Mathlib `CategoryTheory`: 0 hits.
- LeanSearch: `Restriction of scalars commutes with derived inverse limits and derived
  direct image of sheaves of modules`: 8 hits, including ordinary
  `ModuleCat.restrictScalars`, `ModuleCat.preservesLimit_restrictScalars`, and presheaf
  scalar restriction; none states this normalized derived square.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and upstream-name records for
  the item id, `FlatScalarLimitCoherence`, and `flatScalarDirectImageLimitCoherence`
  found no existing declaration of this item. Broader scalar/limit searches found
  the recorded comparison dependencies, localization-colimit modules, and unrelated
  completed-tower constructions; their statements do not give this general equality.

No mathematical node correction or disputed statement was required. Only the item's
`lean` record and the additional already-landed definition dependency are changed.
The two public instance helpers `moduleAbelian` and `moduleLimits` reuse existing
Mathlib instance values by `inferInstance`. They cache compact instance terms while
elaborating the comparison, introduce no assumption, and construct no new mathematical
category or limit. All other helpers are the transparent abbreviations listed above.
The module's sole postponed proof is the named theorem for this node.

Validation: the prescribed `scompile.py NU lem-cbc-flat-scalar-direct-image-limit-coherence`
completed cleanly on the final module, both its sandbox check and its library-name check;
the library-name compile reported 38.4 seconds. There were no errors or warnings.
The initial attempts identified and repaired index-universe misuse and excessive
unfolding of the representative-level expressions. The final theorem keeps the
required model specification through its explicit ordinary and derived-unit equations.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
