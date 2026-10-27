## Worker report

The module `Sheaf.CategoryTheory.RingedCounitFromCohomology` states
`CategoryTheory.RingedToposMorphism.counit_isIso_of_cohomology`, with `sorry`.
Its helper `exactModuleDerivedAdjunction` instantiates the existing canonical
unbounded adjunction, supplying K-injective resolutions from the published
small-site Grothendieck theorem. Its data is that existing adjunction, with no
postponed proof, arbitrary map, chosen nonunique existence witness, or extra
resolution hypothesis. The item statement, dependencies, and proof are unchanged.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 0D7S,
`lemma-bounded-in-image-upstairs`, statement and full proof, lines 6343–6365.
It tests the actual adjunction counit on each cohomology sheaf, then uses finite
Postnikov induction and the degreewise comparison with upper truncations.

Clause-by-clause correspondence:

- The small sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]`
  with Grothendieck topologies `J` and `T`. Their module universe is also `u`.
  A Grothendieck topology is the existing sheaf-site encoding; no global
  pullbacks or functor between the presented sites are required.
- The commutative coefficient sheaves are `A : Sheaf J CommRingCat.{u}` and
  `B : Sheaf T CommRingCat.{u}`. `sheafCompose ... (forget₂ CommRingCat RingCat)`
  merely forgets commutativity for the recorded module and morphism interfaces.
- The geometric morphism and structural ring map are the recorded
  `f : RingedToposMorphism ... A ... B`. Its `f.modules` is the induced module
  direct image, with the underlying sheaf and structural-map action fixed by
  the definition; it is not an unconstrained functor.
- `L` and `adj : L ⊣ f.modules` specify module pullback through its adjunction
  universal property. A left adjoint to this fixed induced direct image is
  precisely module pullback, uniquely up to the unique adjunction-compatible
  isomorphism. This is a presentation of the pullback already named by the node,
  not an additional geometric assumption or a replacement by an arbitrary map.
  Both the hypothesis and conclusion use the same adjunction and its counit.
- `[L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]` render
  exact module pullback. Additivity is intrinsic to that module pullback;
  preservation of finite limits and colimits is the exact-functor interface
  between these abelian module categories.
- The two `[HasDerivedCategory.{wA} ...]` and
  `[HasDerivedCategory.{wB} ...]` select the ordinary unbounded localizations.
  The morphism universes `wA` and `wB` are independent. `K` belongs to the
  source-topos module derived category, exactly `D(A)` in this notation.
- `exactModuleDerivedAdjunction A B f L adj` is literally
  `adj.mapDerivedCategoryRightDerivedAdjunction`, using the proved canonical
  K-injective instance. Its left functor is `L.mapDerivedCategory`, the
  termwise derived exact pullback. Its right functor is
  `f.modules.rightDerivedFunctor`, computed by K-injective resolutions.
  Its unit and counit are the canonical derived unit and counit; neither is
  supplied as additional input. The helper contains no copied construction.
- `hK : ∃ a : ℤ, ∀ q : ℤ, q < a → IsZero (...)` is the stated lower bound
  on every cohomology object. `DerivedCategory.homologyFunctor _ q` is `H^q`.
- `hH : ∀ q : ℤ, IsIso (...counit.app ((DerivedCategory.singleFunctor _ 0).obj
  ((DerivedCategory.homologyFunctor _ q).obj K)))` tests every cohomology sheaf
  placed in degree zero, including negative q. It is not a test on the
  cohomology of the counit or on an underived counit.
- The sole conclusion `IsIso (...counit.app K)` is invertibility of the
  same canonical derived counit at `K`.

Statement dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`: geometric adjunction, structural map,
  and its specified induced additive module direct image.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: recorded site convention;
  the statement uses the Grothendieck topology/sheaf encoding retained by it.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.singleFunctor`;
  and `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`.
- `def-weil-size-convention` is metatheoretic: implemented by explicit
  `u wA wB`, without a duplicate definition or a smallness assumption
  stronger than the small-site statement.

Canonical construction used:
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
The helper supplies `SheafOfModules.isGrothendieckAbelian` from
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, then
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`
from `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
These are real published proofs; no new theorem is postponed for the helper.

Every recorded available proof dependency is imported: the generalized
ringed-site K-injective theorem; Mathlib exact-functor factorization (publicly
through the canonical adjunction) and homology preservation; upstream right
 derived triangulatedness; `exactDerivedAdjunction_isGE`;
`SheafOfModules.module_pullback_pushforward_adjunction`;
`canonicalRightDerivedAdjunctionShift`; and
`DerivedCategory.Plus.heart_test_bounded_below`. Proof-only imports are plain
`import`. The canonical adjunction and its construction prerequisites are
public because they define the helper used by the statement.

Edge cases checked before writing: the zero complex and the zero coefficient
ring; empty sites and degenerate topoi; identity geometric morphism; a sheaf
in any positive or negative degree; negative lower bounds; arbitrary negative
cohomology indices; and complexes bounded below with infinitely many nonzero
positive cohomology objects. None is excluded by the signature. No upper
bound, full faithfulness, conservativity, finite cohomological dimension,
monoidal structure, or preservation of infinite limits is assumed.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`, query: “For a flat ringed topos morphism the
  canonical derived counit is invertible on a bounded below complex if
  invertible on every cohomology sheaf”. Eight hits: exact-functor
  factorization, localization/quasi-isomorphism facts, bounded-below
  representative existence and dense-subsite counit. No exact statement.
- `msearch.py ... loogle`, query: `"counit", "DerivedCategory"`.
  Zero hits.
- `msearch.py ... grep`, query:
  `(counit|Counit).*(bounded|cohomology)|bounded.*counit`,
  subdirectory `Algebra/Homology`. Zero hits.
- `msearch.py ... leansearch`, query: “For an exact module pullback the
  canonical derived counit is invertible on a bounded below complex whenever
  it is invertible on every cohomology sheaf”. Eight hits: ordinary sheaf
  pullback and adjunction, total-left-derived counit, and related comparisons.
  No exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, queries for ringed counits,
  cohomology and bounded counits, identified the canonical derived adjunction,
  the generic heart test and exact-derived bounds. None states this item.
- Search by the exact item id in `lean/WeilConjectures`: no hit.
- Full declaration-name searches for `exactModuleDerivedAdjunction` and
  `counit_isIso_of_cohomology` in Mathlib, upstream, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no collision.

No new nodes, dependency repair, statement correction, or disputed claim.
The file compiled cleanly through `scompile.py Q29
lem-sfb-ringed-counit-from-cohomology`, in sandbox and library module modes
(8.6 seconds and 7.7 seconds). No auto-bound implicits: `autoImplicit false`.

## Second reading by Q29

Performed a second self-audit with the node, source and final Lean file open;
no additional agent was started, as required by the dispatch brief.
The direction is D(B) → D(A) for L and D(A) → D(B) for the derived direct
image, so the counit has target K in D(A). The commutative ring sheaves,
small-site universe, independent localization universes, exactness, existential
integer lower bound, every integer cohomology index, degree-zero single
functor and canonical counit components match all clauses of the node.
The helper's only choice of data is the already constructed canonical derived
adjunction, not a mere Nonempty adjunction. The ordinary `adj` is an explicit
presentation of module pullback with its adjunction; it does not assume any
extra comparison or invertibility. The theorem's proof alone is `sorry`;
the helper contains a real body using named published theorems.
No mismatch was found and no statement change was made.
