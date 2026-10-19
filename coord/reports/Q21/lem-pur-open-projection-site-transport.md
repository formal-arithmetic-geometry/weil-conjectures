## Worker report

This repairs the returned immutable head `8a983e8f8fda`. The saved packet was first
inspected and its prescribed dry run passed at `19a86e04a4`; that mechanical pass did
not resolve the independent reader's mathematical findings. The module and record
were therefore repaired substantively. Only the item's Lean module, its `lean`
record and this report change. The natural-language DAG statement is unchanged.

The module `Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport` states
`AlgebraicGeometry.ProEtale.openProjectionSiteTransport`. Its sole postponed proof
is the entire proof of that named theorem. All five helper definitions have real
bodies, source/blueprint docstrings and entries in `lean.declarations`.

Hypothesis and object correspondence:

- The finite commutative ring A is `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`.
- The scheme T is `X : Scheme.{u}`; `j : U ⟶ X` has `[IsOpenImmersion j]`.
- L is `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- Fixed finite rank is `t : ℕ`. The hypothesis `hL` is now
  `SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
  (R := finiteCoefficientEtaleRingSheaf U Λ)
  ((finiteCoefficientEtaleRealization U Λ).obj L) t`.
  The canonical realization regards L as a sheaf over the associated constant ring
  sheaf; it does not replace L by another arbitrary module. The rank predicate
  requires local free generators indexed by types equivalent to `Fin t`.
  Hence it says exactly that L is locally isomorphic to A_U^t. Rank zero is allowed.
- The integer shift is `m : ℤ`. The first argument to `OpenProjectionTransport`
  is `((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧`, exactly F = L[m].
- G is in `DerivedCategory.Plus` on the etale fixed-ring module category. Its
  unbounded realization is `DerivedCategory.Plus.ι.obj G`. There is no flatness,
  finite Tor-amplitude, constructibility or bounded-above assumption on G.
- In `OpenProjectionTransport`, Fp and Gp are the termwise comparison inverse
  images of F and G. These use the same exact functor as the recorded
  `siteComparisonDerivedPullbackPlus`, with the D+ inclusion omitted so the two
  transport equalities are interpreted in the unbounded categories first.

Conclusion correspondence (unfold `OpenProjectionTransport`):

- The first four conjuncts are `DerivedCategory.TStructure.t.plus` for the source
  and target of κe and κp. `DerivedCategory.Plus` is exactly the full subcategory
  of this predicate. In particular the source clauses include the extension j_!,
  rather than stopping at the unextended tensor on U as the returned packet did.
- κe and κp are the existing `derivedOpenImmersionLowerShriekProjectionMap`
  components. Their definitions are the adjunction transposes of η tensor 1,
  followed by inverse derived tensor/pullback comparison, as the node prescribes.
- γe and γp are now inverse components of the **recorded canonical**
  `derivedOpenImmersionLowerShriekProjectionIso` on the two sites. The recorded
  `lem-pur-etale-open-derived-tensor` note identifies this inverse as the forward
  projection of Stacks 0GL1/0E8I. The pro-etale module's full docstring explicitly
  identifies its inverse as the blueprint's forward projection. Thus these maps
  are the established canonical forward maps, with identity restriction under
  the open-unit identifications, not freshly chosen inverses of arbitrary maps.
  Their source construction computes them from the ordinary projection on K-flat
  total tensors. The statement explicitly includes all four `IsIso` facts and
  the four inverse equations κσ ≫ γσ = id and γσ ≫ κσ = id.
- `openProjectionExtensionComparison` is derived e_j: apply
  `Functor.mapDerivedCategoryNatIso` to the recorded adjunction-normalized
  `openImmersionLowerShriekComparisonUpperStarIso`, with the canonical
  `mapDerivedCategoryCompIso` on both ends. There is no choice of e_j.
- `openProjectionRestrictionComparison` is C_U Lj_e^* ≅ Lj_p^* C_X, obtained
  by descending `comparisonUpperStarCompUpperStarIso` and composing with
  `leftDerivedUpperStarIsoMapDerivedCategory` on both sites. It is the specified
  inverse-image comparison, including its canonical identifications with the
  exact pullbacks.
- `openProjectionSourceComparison` first applies derived e_j to F tensor Lj*G,
  then j_! of the comparison's canonical derived tensor isomorphism, then j_! of
  tensoring Fp with `openProjectionRestrictionComparison`. Its type is exactly
  C_X(source κe) ≅ source κp.
- `openProjectionTargetComparison` first applies the comparison's canonical
  derived tensor isomorphism to (j_!F, G), then tensors derived e_j(F) with the
  identity of Gp. Its type is exactly C_X(target κe) ≅ target κp.
- The last two conjuncts are literal commuting-square equalities
  `C_X.map κe ≫ target.hom = source.hom ≫ κp` and
  `C_X.map γe ≫ source.hom = target.hom ≫ γp` with those explicit isomorphisms.
  The old existential `SiteTransportSquare` is removed entirely. No free
  isomorphism variable occurs in the result.

Return points repaired:

1. `hL : True` was removed and replaced by the actual fixed-rank local-freeness
   predicate above. The reader's Z/4, L = Z/2 counterexample now fails hL. G = Z/2
   remains allowed when L is free; the statement imposes no condition on G.
2. Existential transport isomorphisms were replaced by the four explicit
   canonical-comparison constructions above, all recorded in `lean.declarations`.
3. The forward maps are read from the recorded canonical projection isomorphisms;
   the module docstring and the preceding correspondence justify their forward
   normalization from those interfaces. The inverse equations are explicit.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, together with
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the fixed-ring
  `Etale.DerivedCategoryModule` presentation, and Mathlib's `DerivedCategory`,
  `DerivedCategory.Plus` and `DerivedCategory.TStructure.t.plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientEtaleRealization` and its canonical coefficient-ring
  construction. The node explicitly asks for ordinary fixed-ring module sheaves,
  so tensors and open maps use the equivalent `Sheaf ... (ModuleCat Λ)`
  presentation, not an unrelated small-site or coefficient model.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and the pro-etale tensor
  module: the existing unbounded K-flat derived tensor bifunctors, used by the
  projection modules and the source/target comparisons.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, the restricted exact comparison;
  its underlying unbounded functor is `comparisonUpperStar.mapDerivedCategory`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `Etale.derivedOpenImmersionLowerShriekProjectionMap` and
  `Etale.derivedOpenImmersionLowerShriekProjectionIso`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`:
  `ProEtale.derivedOpenImmersionLowerShriekProjectionMap` and
  `ProEtale.derivedOpenImmersionLowerShriekProjectionIso` (the module recorded
  for `lem-cbc-extension-zero-projection-formula`).
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`, the same canonical e_j
  reexported by the recorded `ProEtaleExtensionZeroComparison` interface.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal`:
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`. Its body uses
  precisely `Functor.leftDerivedTensorComparison` and the canonical identification
  of the total derived comparison inverse image with its termwise exact functor.
- `comparisonUpperStarCompUpperStarIso` and both sites'
  `leftDerivedUpperStarIsoMapDerivedCategory`: the inverse-image comparison.
- Both sites' `openImmersionLowerShriekUpperStarAdjunction` and
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`, already used by the
  canonical projection definitions. The recorded intrinsic pro-etale adjunction
  is the canonical coefficient realization of this fixed-scalar adjunction.
- The recorded general tensor/pullback theorem
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  was read through `scompile.py --source`; it retains independent site object/Hom
  universes and the K-flat total-tensor characterization. Its fixed-ring instance
  is the canonical derived tensor comparison above; no extra universe equality
  is imposed and no new tensor/pullback operation is invented.

The initially tried standard ComparisonMonoidal import mixes the standard and
finite-coefficient copies of upperStarIsoLowerStarInv in the published environment.
The current server sources were read through `scompile.py --source` and imports
were switched consistently to the existing finite-coefficient owners of the same
canonical operations. No published source was edited and no duplicate declaration
was added to work around the collision.

Edge cases checked: t = 0 and the zero sheaf; m = 0 and arbitrary negative or
positive shifts; identity and empty open immersions; zero G; the zero coefficient
ring; and finite nonregular rings such as Z/4. Local finite freeness ensures
boundedness for free L over Z/4 even with G = Z/2; the reader's nonfree L is
excluded for exactly the missing reason. The two canonical square constructions
remain meaningful for all these cases. All coefficient and site universes are
explicit; the actual small pro-etale site `Scheme.ProEt.topology` is retained.

Searches made: the saved packet searched `msearch.py leanfinder` for "site transport
normalized open tensor projection derived categories" and found only general
monoidal-site declarations; project grep found no exact declaration tagged with
this item. In this repair, `msearch.py leanfinder` for "sheaf of modules locally
isomorphic to a fixed finite free module of rank t" returned local generators and
free-sheaf interfaces; the fixed-rank predicate was then found and its full source
read in the upstream LocallyFree module. `msearch.py loogle` for
`SheafOfModules.IsFiniteLocallyFreeOfRank, Sheaf` returned unknown identifier
(the service lacks this project extension). `msearch.py grep` for
`openProjectionSiteTransport|SiteTransportSquare|openProjectionSourceComparison`
in Mathlib CategoryTheory returned no hits; `rg` for the same names in the upstream
WeilConjectures source and `lean/Sheaf` returned no hits. Direct source inspection
and current-server `scompile.py --source` found all canonical comparisons used.
No new notion or dependency node was needed. No STATEMENT-DISPUTED marker.

## Second reading by Q21

A separate self-check pass reread the natural-language node, the returned defects,
the entire revised module and the canonical source signatures. No additional
agent was started, as the dispatcher brief prohibits it. Each ring, scheme,
open-immersion, rank, shift and D+ hypothesis is matched above. The old empty
hypothesis, arbitrary isomorphism square and unextended source-boundedness clauses
were defects and were changed. The two new comparison isomorphisms have the
correct source and target, and the square orientations agree with κ and γ.
The forward projections use the already recorded, source-normalized isomorphisms,
whose inverse orientation is explicitly documented upstream. The statement has
no resolution choice, arbitrary map or nonempty-isomorphism choice. All helpers
are real constructions, and only openProjectionSiteTransport has a sorry. The
item's node statement, dependencies and proof plan remain unchanged.

Validation: the repaired file passed `scompile.py Q21
lem-pur-open-projection-site-transport <module>` without errors or warnings:
sandbox pass 21.3 seconds and library pass 7.8 seconds. The fixed-rank predicate
has explicit coefficient universe u+1, site Hom universe u and site object
universe u+1; this fixes an initial universe-inference diagnostic without changing
any mathematical hypothesis. A source/record check confirms that only `lean`
changes in the node, all six declarations are listed, all source lines are at
most 100 columns, and there is exactly one sorry, on the named item theorem.
