## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleChartCompactSupportNormalization` states
`AlgebraicGeometry.Etale.etaleChartCompactSupportNormalization`, with proof `sorry`.
Its fully written Prop-valued helper `EtaleChartCompactSupportNormalization` packages
exactly the coefficient, geometric and normalized functor assertions of this node.
There are no new independent notions, dependency repairs or statement corrections.

Source read: the whole current main-20261015 exceptional-reduction proof at the node's
source path, especially Locality and Charts, and Stacks `more-etale.tex`, labels
`lemma-shriek-proper-and-open` (0F7B) and `lemma-shriek-composition` (0F7J).
The source's Locality paragraph supplies the source-open normalization; the node's
closed-chart supplement expands its arbitrary-map factorization. The source agrees
with the node; no statement is disputed.

Hypothesis-by-hypothesis and clause-by-clause translation:

- `ell : ℕ`, `[Fact ell.Prime]`, `[Algebra (Padic ell) E]` and
  `[FiniteDimensional (Padic ell) E]` specify the prime and finite coefficient extension.
  `E : Type (u + 1)` places its quotient in the established coefficient universe of
  the small-etale module categories; a smaller finite extension can be lifted.
- `n : ℕ`, `hn : 1 ≤ n`, and `Padic.coefficientExtensionRing ell E n` give
  the dependency's actual valuation-ring quotient by its chosen uniformizer power.
  No new coefficient ring, valuation or uniformizer is chosen in this delivery.
- `k : Type u`, `[Field k]`, `p : ℕ`, `[CharP k p]`, `hp : 0 < p` and
  `hell : ell ≠ p` give all the characteristic assumptions.
- `[X.Over (Spec (.of k))]`, `[Y.Over (Spec (.of k))]`, separatedness, local finite
  type and quasi-compactness of both structure maps give separated finite-type
  k-schemes. `f : X ⟶ Y` and `[f.IsOver (Spec (.of k))]` give the k-morphism.
- `u : U ⟶ X`, `v : V ⟶ Y`, their `IsOpenImmersion` instances and `[IsAffine U]`,
  `[IsAffine V]` give precisely the affine open charts. The induced structure maps
  are composed explicitly, so no additional chosen k-structures on U,V are required.
- `r : ℕ` includes rank zero; `AffineSpace (ULift.{u} (Fin r)) V` is P and
  its canonical `↘ V` is pi, exactly the recorded affine-space specialization.
- `i : U ⟶ P`, `[IsClosedImmersion i]`, and
  `h : u ≫ f = (i ≫ (P ↘ V)) ≫ v` give the closed chart and its commutativity.
- `W : Scheme`, `j : W ⟶ P`, `[IsOpenImmersion j]`, and
  `hij : Set.range i.base = (Set.range j.base)ᶜ` express the complementary open.
  Allowing any presentation of that open is the invariant version of W=P-i(U).
- The helper's first conjunct is `Finite A`; its second is `(N : A) = 0`,
  specialized to `N = ell ^ n`. Neither is assumed in the theorem.
- The first dependent finite list explicitly enumerates the six schemes and their
  induced k-structure maps. For each, it asserts `IsNoetherian`,
  `LocallyOfFiniteType` and `QuasiCompact` of the structure map, and
  `IsUnit (N : Γ(S, ⊤))`. Global invertibility is exactly invertibility of the
  constant integer on the scheme. Mathlib's `IsNoetherian` is locally Noetherian
  plus quasi-compact; `isNoetherian_iff_of_finite_affine_openCover` gives exactly
  the finite-affine-cover description in the node, with `IsNoetherianRing` rings.
- The second dependent finite list enumerates u,v,j,f,i,pi, the composites u;f,
  i;pi, i;pi;v, pi;v, j;pi and j;pi;v, and all six structure maps to Spec k.
  It asserts separatedness, local finite type, quasi-compactness and
  `HasCompactification` for each. In particular u,v,j are quasi-compact.
  The lists quantify over membership, without requiring distinct schemes/maps:
  identities and coincident vertices remain valid.
- `PreservesFiniteLimits (lowerStar ... i)` and `PreservesFiniteColimits ...`
  explicitly assert exactness of closed direct image. Its appearance as
  `(lowerStar ... i).mapDerivedCategory` is exact termwise application, not just
  an unnamed right derived functor.
- The final clause universally binds the finite-ring, quasi-compactness and
  compactification instances already asserted above. This only allows the
  consequence-dependent functor types to elaborate: the preceding conjunction
  ensures these types are inhabited, so the clause cannot be vacuous and imposes
  no extra hypotheses on the theorem. It applies for every such proof instance.
- `au` and `av` are adjunctions between exact derived open extension and exact
  derived pullback. Their equalities to
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` specify the ordinary
  adjunctions, including their evaluation counits, rather than bare adjointness.
- `e` is a natural isomorphism `D(u_!) ⋙ Rf_! ≅ (D(i_*) ⋙ Rpi_!) ⋙ D(v_!)`
  between entire derived categories. Its equality fixes precisely the requested
  composite: inverse source-open identification, alpha(f,u), chart equality,
  inverse alpha(v,pi i), whiskered inverse alpha(pi,i), the canonical
  proper-support-to-direct-image comparison and the exact finite direct-image
  comparison, and finally the target-open identification. Functor composition
  is written left-to-right in Lean, the reverse of the printed mathematical notation.
- The existential family `μ cf cp` gives this isomorphism in every pair of
  compactification models for f and pi. Its first equation defines it by the
  model-to-chosen comparisons and e; its second is the complete commuting square
  under arbitrary changes cf→cf' and cp→cp'. In particular it holds for proper
  refinements and common refinements, explicitly expressing refinement independence.
  Open factors have the identity-proper normalization and the closed factor the
  canonical proper comparison; these are fixed rather than varied arbitrarily.
- There is no D-plus inclusion, constructibility condition, t-structure interval
  or boundedness assumption anywhere in these types.

Dependency declarations read and used:

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; signature and docstring read in its recorded module.
- `def-weil-pbc-scheme-conventions`: convention node; Mathlib `Scheme`, `IsOpenImmersion`,
  `IsClosedImmersion`, `IsAffine`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsNoetherian`, and the usual composition of scheme maps.
- `def-sbc-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace` and its `over` projection, coordinate type ULift (Fin r).
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`; signature and docstring read in its recorded module.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`; signature and docstring read in its recorded module.
- `lem-exc-closed-support-triangle`: `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`,
  `AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle`; signature and docstring read in its recorded module.
- `lem-amb-unbounded-compact-support-comparisons`: `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
  `AlgebraicGeometry.Etale.unboundedEtaleCompactSupport_baseChange`; signature and docstring read in its recorded module.
- `lem-amb-compact-support-open-source-composition`: `Sheaf.AlgebraicGeometry.OpenSourceComposition`,
  `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_open_source`; signature and docstring read in its recorded module.
- `lem-sfb-quasifinite-compact-support-exact`: `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`,
  `AlgebraicGeometry.Etale.quasifiniteCompactSupportExact`; signature and docstring read in its recorded module.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; signature and docstring read in its recorded module.

In the comparison package, the specific declarations used are
`unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekCongr`,
`rightDerivedLowerShriekIso`, and `rightDerivedLowerShriekOfCompactificationIso`.
The source-open theorem is `unboundedEtaleLowerShriekCompIso_open_source`.
The exact closed normalization uses
`rightDerivedLowerShriekIsoRightDerivedLowerStar` from
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar` and
`rightDerivedFunctorLowerStarIsoMapDerivedCategory` from
`WeilConjectures.SixFunctors.Finite.Exact`. The former is the canonical forget-supports
comparison for a proper map; the latter is the canonical exact-functor derived
comparison, so together they realize the proper specialization of the recorded
quasi-finite support comparison, without selecting an unconstrained iso.
`rightDerivedLowerShriekIsoOfIsOpenImmersion` from
`WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` uses precisely
its identity-proper compactification. `DerivedCategoryModule` is the recorded
ordinary ModuleCat-valued small-etale encoding. All stated proof dependencies are
imported as part of the future proof plan, using their actual Mathlib files where
there is only a mathlib_match.

Searches actually run (the msearch wrapper saved its results in searches.jsonl):

- LeanFinder: "Canonical unbounded etale compact support composition with open
  extension by zero and closed immersion direct image": 8 results, chiefly
  `Scheme.Hom.liftCoborder` and topological compact support, no matching statement.
- Loogle: "CategoryTheory.Functor.isoWhiskerLeft,
  CategoryTheory.Functor.isoWhiskerRight": 12 results about generic whiskering,
  including `isoWhiskerLeft_trans_isoWhiskerRight`; none is this statement.
- msearch grep: "etaleChartCompactSupport|closedChartCompactSupport|
  rightDerivedLowerShriekIsoOfIsClosedImmersion": 0 Mathlib hits.
- LeanSearch: "Canonical composition of derived etale compact support with open
  extension and closed direct image": 8 hits, including topological support,
  O-module `SheafOfModules.pushforwardComp`, and scheme restriction composition;
  no ordinary etale compact-support normalization.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and chart
  compact-support names: no upstream statement. The parent module contains
  `closedChartCompactSupportComparison`, which gives the same canonical composite
  ending at Ri_* but neither the coefficient/geometric conclusions nor this full
  normalization assertion. The parent's proof_deps includes this item, so importing
  that module would create a future proof-import cycle. This delivery defines no
  duplicate chart map; e is quantified and fixed directly by existing factors.
  The already landed bounded-below `EtaleChartLeftCompositor` is not an unbounded
  normalization with these coefficient/geometric conclusions.

Edge cases checked before and after writing: r=0 (Fin 0), U empty, V empty and
hence P empty, W empty (surjective closed immersion), i identity, u or v identity,
n=1 and ramified E (ell^n still kills the quotient even when ell is not itself a
uniformizer), nonreduced closed charts, coincident scheme vertices in the two lists,
and arbitrary unbounded complexes. No reducedness, smoothness, purity, cohomological
finiteness or nonempty-chart assumption was added. n=0 is excluded exactly as in the
node. Positive characteristic with ell!=p is retained even though the functorial
comparison itself is more general.

Validation: scompile.py compiled both the sandbox and library-context checks cleanly;
only the expected theorem sorry is postponed. `autoImplicit false` is enabled and
all universes and variables are bound. No global build, direct git command or live
source edit was run.

## Second reading by Q58

The dispatch expressly prohibits starting other agents and assigns independent review
to the maintainer. The following is a separate self-reading, not a claim that another
worker reviewed this delivery. The maintainer's independent reading remains required.

I reread the item and the final module side by side. All coefficient and characteristic
hypotheses, both separated finite-type structure maps, the k-linearity of f, both affine
open hypotheses, rank zero, the closed chart equality and complement range equation
are present in the theorem. The first version represented exact i_* by its derived
functor comparison, but did not separately assert exactness; the final version adds
both finite-limit and finite-colimit preservation and ends e at mapDerivedCategory.
The first version fixed e by its composite but left refinement independence to the
imported coherence theorem; the final version includes μ and its explicit commuting
square. I also added the six k-structure maps to the arrow list, so compactifiability
of these displayed composites is explicit. No source hypothesis became a conclusion
or conversely. The two list-membership quantifiers work with repeated and empty
schemes, and the asserted consequence instances make the last universal clause
nonvacuous. The parent map was inspected only as a cross-check, not imported or
redefined. The final module compiles after these repairs. No node statement changed.
