## Worker report

The module `Sheaf.SixFunctors.OpenScalarConjugateNormalization` states
`AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization`, with one
postponed proof and no new definitions. The DAG statement is unchanged.

Hypothesis and clause correspondence:

- A morphism of commutative condensed rings is represented by
  `Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, their `MonObj` and
  `IsCommMonObj` instances, and `a : Λ ⟶ Λ'` with `[IsMonHom a]`.
- Arbitrary schemes and their open immersion are `{U X : Scheme.{u}}`,
  `(j : U ⟶ X)` and `[IsOpenImmersion j]`. There is no base field, finite-type,
  quasi-compactness, separatedness, flatness, or boundedness hypothesis.
- The pulled-back coefficient rings are exactly `condensedRingObj Λ U` and its
  other three specializations. The coefficient change is the published `coefficientMap a T`.
- The ordinary unbounded derived category is Mathlib's `DerivedCategory` of the
  published internal module category `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
  (condensedRingObj Λ T)`. No bounded or completed category is substituted.
- `T_T` is exactly `L(Mod.extendScalars (coefficientMap a T))`, expressed by the inline
  projection `(fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)` applied to the published
  `Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a T)`. This reduces
  definitionally to that same functor and avoids repeating its tensor instance search.
  No new scalar functor or notion is defined.
  Pullback is `D((j)^*⟦Λ⟧)` and extension by zero is `D((j)_!open⟦Λ⟧)`.
- `θ` has source `D(j_A^*) ⋙ T_U` and target `T_X ⋙ D(j_B^*)`.
  Its forward map is constrained by an equality to
  `SheafOfModules.ScalarPullback.mate` for the published derived scalar adjunctions
  applied to `(derivedComapUpperStarIso a j).inv`. This is the precise scalar-adjunction
  mate in the node, rather than the flat-only `derivedPullIso`. The K-flat dependency
  identifies this mate with the balanced tensor comparison, after alpha and the fixed
  internal/sectionwise transport.
- `β` is used literally as `(derivedOpenImmersionShriekIso a j).hom`, without an
  independently chosen isomorphism. Its definition is the composite-adjunction
  conjugate of the recorded `derivedComapUpperStarIso`.
- The isomorphisms `uA` and `uB` have precisely the identity and `D(j_!) ⋙ D(j^*)`
  endpoints. Their homs equal the units of
  `derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j` and its Λ' version.
- The existential binders package the specified invertible mate and actual invertible
  units together with the equalities fixing their homs. They are conclusions, not
  extra assumptions or freely chosen normalizations: an isomorphism is determined by
  its hom. This expresses the node's given invertible comparisons while avoiding
  unproved local typeclass instances or helper theorems lacking DAG nodes.
- For every unbounded `M`, Lean's left-to-right composition writes the node's formula as
  `D(j_B^*).map (β.hom.app M) ≫ uB.inv.app (T_U.obj M) =
  θ.inv.app (D(j_!A).obj M) ≫ T_U.map (uA.inv.app M)`.
  It is an equality of components of the specified natural transformations for every
  object; all maps are natural, giving exactly the stated natural identity.

Dependencies read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `AlgebraicGeometry.ProEtale.coefficientMap`,
  `CondensedRing.derivedComapUpperStarIso` and
  `CondensedRing.derivedOpenImmersionShriekIso`; their full definitions confirm the
  coefficient square, levelwise localization, and exact composite-adjunction conjugate.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.isIso_condensedPullbackHom`; alpha is invertible for every
  scheme morphism, not just open immersions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`, its exactness, and the actual adjunction;
  its derived version is in `ModuleObject.Derived.OpenImmersionLowerShriek`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.mate` and
  `kflat_scalar_comparison_normalization`; the former is the inverse Mathlib mate
  operation and the latter fixes the balanced K-flat normalization used in proof step 5.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` supplies the recorded
  derived-category convention interface. The assertion uses the ordinary `DerivedCategory`
  and the already published scalar and exact derived functors, not a new derivation.
- Proof imports include `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`,
  with `AlgebraicGeometry.ProEtale.InternalModuleOperations.internal_module_operations_transport`.
  The other stated proof dependencies are exported by the above upstream modules:
  `comapUpperStarIso`, `Mod.extendScalarsComapIsoOfIsIso`, `Mod.extendScalars`,
  module pullback/pushforward, `Functor.ProjectionFormula`, `conjugateIsoEquiv`,
  `mateEquiv`, and `Adjunction.comp`. The proof-only node
  `lem-sfb-internal-section-scalar-adjunction` currently has no recorded declaration,
  so it contributes no import. No missing notion is needed to type this statement.

Source checked: current blueprint
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md`,
clauses (1) and (2), and the current blueprint definition
`sk-def-sfb-coefficient-comparisons/def-sfb-derived-open-immersion-shriek-iso.md`.
The docstring records all seven DAG proof steps, including the action-square check,
internal/sectionwise transport, composite-unit calculation, and final cancellation.

Edge cases checked mathematically and against the binders: identity open immersion,
empty open, zero object M, zero coefficient ring, identity coefficient change, and
nonflat coefficient changes such as the condensed Z to Z/2 map. None is excluded.
There is no `Nontrivial` assumption. The site uses the published `Scheme.{u}` and
`Ab.{u + 1}` size convention. The hom equation for θ retains the specified adjunctions;
changing θ by a unit automorphism would violate that equation.

Searches (all launcher searches logged in `searches.jsonl`):

- `msearch.py ... leanfinder`: "Restriction of the specified derived open extension by
  zero scalar conjugate is the inverse scalar adjunction mate under the open adjunction
  units". Eight hits about ordinary ModuleCat scalar adjunctions; no exact result.
- `msearch.py ... loogle`: `CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv`.
  Four generic mate/conjugate pasting lemmas; none identifies this geometric comparison.
- `msearch.py ... grep`: `unit_conjugateEquiv|unit_mateEquiv|derivedOpenImmersionShriekIso`
  in Mathlib CategoryTheory. Seven generic unit/mate hits; no geometric normalization.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the two published derived comparison
  names found the upstream constructions, integral specializations, and
  `Sheaf.SixFunctors.ScalarSixPullback`. The latter defines the canonical mate
  `scalarSixPullHom` but its umbrella theorem includes extra geometric coherence data
  and standing finite-type hypotheses; it does not state this node's unrestricted
  formula for the specified open conjugate. It is downstream and is not imported.
  The statement uses the already recorded generic `ScalarPullback.mate` directly,
  creating no second scalar comparison definition.
- Exact node-id search in `lean/WeilConjectures` found no declaration. Searches for
  `openScalarConjugate`, `open_scalar_conjugate`, and scalar conjugate normalization in
  both source roots and `dag/lean_names_upstream.json` found no existing declaration.

No statement dispute, correction, new node, or dependency repair is needed.

Validation: the first version compiled on current sources in 55.1 seconds but the dry
run subsequently timed out. The final expression projects the left functor from the
already elaborated scalar adjunction, and uses the same transparency options as the
existing scalar-six module. It has the identical mathematical functor and assumptions.
The revised version compiled in 21.6 seconds as a sandbox and 25.9 seconds as the
named library module. The sole long-line warning was then repaired by wrapping that
line; the required dry run recompiles this final formatting. Every variable and universe
is explicitly bound and every Lean line is at most 100 characters.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
