## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization` states
`AlgebraicGeometry.Etale.etaleImmersionShriekNormalization` with proof `sorry`.
Its two helpers `etaleOpenCompactSupportNormalization` and
`etaleClosedCompactSupportNormalization` construct the specified natural
isomorphisms for arbitrary supplied compactifications, with full data and no
postponed construction. No statement correction, new node, or dependency repair
is needed. The node copy changes only `lean`.

The source read is Stacks `more-etale.tex`, Tag 0F7I,
`lemma-shriek-well-defined` (construction and common-refinement coherence), and
Tag 0F51, `lemma-proper-f-shriek`. I also read `etale-cohomology.tex`, Tag 04FX,
`lemma-stalk-pushforward-closed-immersion`, and Tag 03S5,
`proposition-describe-jshriek`. The node deliberately requests only the
bounded-below compactification comparison even though the current Stacks text
also proves an unbounded torsion-coefficient comparison.

Hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`; no nontriviality assumption. |
| Schemes W, Z, T are Noetherian | `{W Z T : Scheme.{u}} [IsNoetherian W] [IsNoetherian Z] [IsNoetherian T]`. Mathlib identifies this with a finite affine Noetherian cover. |
| Open immersion j and closed immersion c | `(j : W ⟶ T) [IsOpenImmersion j] (c : Z ⟶ T) [IsClosedImmersion c]`. |
| Separated finite-type morphisms | These properties follow from the immersion hypotheses: open immersions are separated and locally of finite type; their quasi-compactness follows from the Noetherian source. Closed immersions are finite, hence proper and finite type. No extra assumption or excluded immersion is introduced. |
| Chosen compactifications | `(dj : Compactification j) (dc : Compactification c)`, explicit arbitrary choices rather than a substituted canonical choice. |
| Ordinary unbounded constant-A module-sheaf categories | `DerivedCategoryModule A W`, `DerivedCategoryModule A Z`, and the full `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. This is the recorded six-functor encoding, not a pro-etale or constructible category. |
| j_! and c_* | The dependency declarations `openImmersionLowerShriek (ModuleCat A) j` and `lowerStar (ModuleCat A) c`. |
| Exactness of c_* | First conjunct: `PreservesFiniteLimits ... ∧ PreservesFiniteColimits ...`. The finite-direct-image instance applies to ModuleCat coefficients themselves. |
| Degreewise descent Dj_!, Dc_* | The existing `.mapDerivedCategory` functors. Their defining localization factorization is `Functor.mapDerivedCategoryFactors`, so this names the prescribed termwise descent. |
| Every integer m, all complexes vanishing below m | The next two conjuncts quantify over `m : ℤ` and arbitrary `H : DerivedCategoryModule A W` or `L : DerivedCategoryModule A Z`, and assert `H.IsGE m → ...IsGE m`. No bounded-below restriction is placed on these quantified categories. |
| Natural cohomology comparison for each q | Two conjuncts `∀ q : ℤ, Nonempty (FD ⋙ DerivedCategory.homologyFunctor _ q ≅ DerivedCategory.homologyFunctor _ q ⋙ F)`. These assert natural isomorphisms, rather than unrelated pointwise isomorphisms. Existing canonical witnesses are `(F.mapDerivedCategoryHomologyFunctorIso q).symm`. No data is defined by choosing from these assertions. |
| Normalizations Rj_! ≅ Dj_! and Rc_! ≅ Dc_* on D+ | The two helper definitions have type `DerivedCategory.Plus.ι ⋙ candidate ≅ DerivedCategory.Plus.ι ⋙ exactFunctor.mapDerivedCategory`. Thus the entire natural isomorphism takes values in the ambient unbounded category while its domain is exactly D+. |
| Specified open normalization | `rightDerivedLowerShriekOfCompactificationPlusιIso A d (Compactification.ofIsOpenImmersion j)`, followed by whiskering `rightDerivedLowerStarIdIso A T` by Dj_! and the right unitor. The latter identity is itself constructed by the exact-functor comparison and descent of `lowerStarId`. |
| Specified closed normalization | Compare to `Compactification.ofIsProper c`, whisker `mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat A) Z` by Rc_*, apply the left unitor, and `rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat A) c`. This last map is exactly the canonical inverse of the derived comparison Dc_* → Rc_*. |
| Commutes with morphisms of bounded-below inputs | Both constructed objects are natural isomorphisms of functors with domain D+; their `.hom.naturality` equations give precisely the requested squares. |
| Commutes with all changes of compactification | Final two conjuncts quantify over every `dj'` and `dc'`: `rightDerivedLowerShriekOfCompactificationPlusιIso A dj dj' ≪≫ normalization dj' = normalization dj`, and likewise for c. These use the existing proper-refinement-normalized canonical comparisons, so include identity and refinement cases. |
| Ambient isomorphisms only for bounded-below inputs | Each component of the helpers is an `Iso` in the unbounded derived category, but `Plus.ι` occurs before both candidates. No compactification comparison is asserted on an arbitrary unbounded input. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `Morphisms.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the finite-affine-cover
  specialization is `AlgebraicGeometry.IsNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus` and `homologyFunctor`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, its additivity and exactness instances.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, and its Plus compatibility.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`:
  `etaleCompactSupport_refinementComparison_eq`; the recorded imported comparison
  `rightDerivedLowerShriekOfCompactificationPlusIso`, its cocycle law, and its
  ambient restriction `rightDerivedLowerShriekOfCompactificationPlusιIso` are used.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerStarIdIso`, `mapDerivedCategoryOpenImmersionLowerShriekId`.
- `WeilConjectures.SixFunctors.Finite.Exact`:
  `preservesFiniteColimits_lowerStar_of_isFinite` and
  `rightDerivedFunctorLowerStarIsoMapDerivedCategory`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryHomologyFunctorIso` and `isGE_mapDerivedCategory_obj`.
  Mathlib `Functor.mapDerivedCategoryFactors` and `Localization.lift` supply
  the recorded descent and uniqueness interfaces.
- The module imports the stated proof dependencies
  `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`,
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, and
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`; their full signatures and
  docstrings were read. The direct finite ModuleCat exactness interface avoids
  needing a new comparison with their alternative ULift ring-sheaf encoding.

Edge cases checked before writing: zero coefficient ring; empty source schemes;
zero complexes; all integer lower bounds, including negative bounds; the identity
immersion; the trivial compactifications themselves; changing a compactification
to itself; and arbitrary changes, including proper refinements. No nonempty,
nonzero, positive-degree, constructibility, or invertibility condition appears.
For the trivial compactifications the comparison is the identity by the existing
refl law, leaving exactly the specified identity/exact-functor maps. The natural
cohomology clauses quantify over all integer q and all unbounded inputs.

Searches made (all remote searches through the prescribed msearch.py):

- LeanFinder: “Etale compact support for open immersions equals exact extension
  by zero and closed immersions equals exact direct image, canonical compactification
  normalization”. Eight hits on scheme coborder/normalization and affine sections,
  including `AlgebraicGeometry.liftCoborder_app`; none states this node.
- Loogle: `"mapDerivedCategory", "homologyFunctor"`: zero hits. The upstream exact
  functor API was instead located and read by rg.
- Mathlib grep: `lowerShriek|LowerShriek|extensionByZero|ExtensionByZero` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: “Derived compact support of an open immersion is extension by zero
  and of a closed immersion is the exact direct image, naturally and compatibly
  with changes of compactification”. Eight ordinary topological function-support
  hits, including `HasCompactSupport.extend_zero`; none concerns etale sheaves.
- rg in `lean/WeilConjectures` and `lean/Sheaf` found the generic exact-functor API,
  the canonical compactification comparison API, and
  `Etale.ChartAdjointComparison.openNormalization`, `.closedNormalization`, and
  `.closedNormalizationAmbient`. Those helpers select
  `HasCompactification.compactification` rather than accept the arbitrary supplied
  compactification of this node; they do not state the full lower-bound,
  cohomology, and change-of-compactification package. The new helpers instead
  construct the arbitrary-compactification ambient version directly from the
  existing canonical maps, without importing the downstream chart-comparison node.
- rg for this node id in `lean/WeilConjectures` found no declaration. Searches for
  the three proposed full declaration names in `lean/Sheaf`, `lean/WeilConjectures`
  and `dag/lean_names_upstream.json` found none.

Validation: the initial scompile elaborated both sandbox and destination versions
successfully, with one 103-character line warning; that line was shortened.
The subsequent scompile completed cleanly for both sandbox and destination
versions (26.5 s and 40.8 s), without errors or warnings. The prescribed
`deliver2.py --no-push` then printed OK: the packet compiles and passes the
maintainer preflight. A source-only packet check confirmed that only `lean`
changes in the node, no Lean line exceeds 100 characters, and the recorded
signature matches the theorem verbatim.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
