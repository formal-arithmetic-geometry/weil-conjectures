## Worker report

This repair supplies the missing stage-2 statement module for
`lem-trf-excellent-base-marked-semistable-curve`. The module is
`Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` and its declaration is
`AlgebraicGeometry.exists_excellentBaseMarkedSemistableCurve`, with a `sorry` proof only.
It quantifies integral, excellent and Noetherian source and base schemes, a proper dominant
family, a generic point whose scheme-theoretic fibre has Krull dimension one, and a proper
closed boundary. Its conclusion gives the commutative alteration square, integral excellent
Noetherian altered schemes, proper surjective maps finite over dense opens, and a proper flat
finitely presented family. The geometric-fibre clause is rendered by
`IsSemistableGeometricCurve` at the chosen algebraic-closure geometric point over every point;
this expands to nonempty connected, reduced, pure dimension one fibres, smooth points or
ordinary double points. The generic-fibre clause is an existential generic point with
`Smooth` and `GeometricallyIntegral`. Finitely many sections are represented by `Fin n`, with
section equations, pairwise disjoint ranges, and formal smoothness at every point in each
range (the definition of the relative smooth locus). The proper closed exceptional subset is
`T : Set B'`, and the boundary inclusion is the displayed preimage containment. The `Fin 0`
case gives the empty family of sections and the empty union, so empty boundary and empty
marking are included.

The Lean renders the hypotheses as follows. `[IsIntegral C]` and `[IsIntegral B]` are the
integrality hypotheses; `[IsNoetherian C]` and `[IsNoetherian B]` are the Noetherian
hypotheses; `hC : IsExcellentScheme C` and `hB : IsExcellentScheme B` express excellence
on every affine coordinate ring; `[IsProper f]` and `[IsDominant f]` render proper dominance;
`hgeneric : ∃ η, IsGenericPoint η Set.univ ∧ topologicalKrullDim (f.fiber η) = 1`
introduces the generic point and dimension-one generic fibre; and
`hZ : IsClosed Z ∧ Z ≠ Set.univ` makes `Z` a proper closed subset.

The conclusion clauses are rendered, in order, by `a ≫ f = f' ≫ b`; the six predicates
`IsIntegral`, `IsExcellentScheme`, and `IsNoetherian` for `C'` and `B'`; for each alteration
`IsProper`, `Surjective`, and `∃ U, Dense U ∧ IsFinite (pullback.snd _ U.ι)`; then
`IsProper f'`, `Flat f'`, `LocallyOfFinitePresentation f'`, `QuasiCompact f'`, and
`QuasiSeparated f'`. For every `y : B'`,
`IsSemistableGeometricCurve (pullback.snd f' (geometricPoint B' y))` gives the nonempty connected reduced pure
one-dimensional fibre and its smooth-or-ordinary-double-point alternatives. The generic fibre
is `∃ η', IsGenericPoint η' Set.univ ∧ Smooth (...) ∧ GeometricallyIntegral (...)`.
The marking clause is `∃ n, ∃ s : Fin n → (B' ⟶ C'), ∃ T : Set B'`; its three section
conditions are `s i ≫ f' = 𝟙 B'`, pairwise `Disjoint` ranges, and
`(f'.stalkMap x).hom.FormallySmooth` on each marked point. Finally
`IsClosed T ∧ T ≠ Set.univ` and
`a ⁻¹' Z ⊆ (⋃ i, Set.range (s i)) ∪ f' ⁻¹' T` render the proper closed exceptional set
and the required containment. No projectivity or affineness assumption on `B` is introduced.

The existing declarations used are `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsIntegral` from
`Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsLocallyNoetherian` and
`AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`,
`AlgebraicGeometry.Scheme.Hom.fiber` and `fiberToSpecResidueField` from
`Mathlib.AlgebraicGeometry.Fiber`, `AlgebraicGeometry.GeometricallyIntegral` from
`Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.Flat`,
`LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, and `Smooth` from their
Mathlib morphism modules, `topologicalKrullDim` from `Mathlib.Topology.KrullDimension`, and
`IsGenericPoint` from `Mathlib.Topology.Sober`. The project module
`Sheaf.Paper.OrgogozoInductionData` supplies
`AlgebraicGeometry.Orgogozo.IsExcellentScheme` and
`AlgebraicGeometry.Orgogozo.IsSemistableGeometricCurve`; its latter definition uses the
project's `IsOrdinaryDoublePoint` and `nodeRing`, so no private copy of the nodal notion is
introduced. The dependency declarations in the item node were read before writing and are
used through these imports and standard predicates.

Edge cases checked: `Fin 0` gives no sections and an empty union; a nonempty proper closed
`Z` is handled by the same preimage inclusion; the generic point is explicitly bound rather
than assuming a chosen point; all geometric-fibre quantifiers use the scheme universe `u`,
including arbitrary characteristic and algebraically closed extensions; the dimension-one
condition is retained as an equality rather than weakened to an inequality; and no
projectivity, affineness, or nonempty marking assumption is added. A search for an existing
statement found no declaration with this item id or theorem name in the source or project.

Searches made:

* `msearch.py ... leanfinder "A proper dominant morphism ... marked semistable curve ..."`:
  8 hits, all generic properness, integrality, normalization, or dominance declarations; no
  alteration or marked semistable theorem.
* `msearch.py ... loogle "IsExcellentScheme, IsSemistableGeometricCurve, IsAlteration,
  HasNodalGeometricFibres"`: 0 hits; `IsExcellentScheme` is unknown to Loogle.
* `msearch.py ... grep "smoothLocus|IsSemistableGeometricCurve|IsExcellentScheme|
  exists_excellentBaseMarkedSemistableCurve" AlgebraicGeometry`: 10 Mathlib hits, all
  `smoothLocus` declarations; no matching theorem or project predicate in Mathlib.
* `rg -n "exists_excellentBaseMarkedSemistableCurve|IsSemistableGeometricCurve|
  IsExcellentScheme"` over `WeilConjectures/` and `lean/Sheaf`: only the existing
  `OrgogozoInductionData` definitions and their uses; no existing item statement.
* The dependency node files and every recorded module or `mathlib_match` were opened. The
  source declaration signatures and docstrings were read for all fourteen `stmt_deps`.

The earlier returned head was a stage-1 split with no module or Lean record. This delivery
adds only the stage-2 module, the item's complete `lean` record, and this report; no stage-1
split fields were changed.

## Second reading by Q18

I reread the item statement, the theorem signature, and the full source module after the
successful compile. The input clauses match one-for-one: proper dominant `f`; integral,
excellent, Noetherian `C` and `B`; a generic point and dimension-one fibre; and a proper closed
`Z`. The output rereading checks the square equation, both integral/excellent/Noetherian
altered schemes, both alteration clauses (proper, surjective, finite on a dense open), proper
flat finite-presentation data, every geometric-fibre clause through
`IsSemistableGeometricCurve`, the smooth geometrically integral generic fibre, finite indexed
sections with section equations and disjointness, relative smoothness at section points, the
proper closed `T`, and the exact boundary containment. I checked the empty `Fin 0` marking,
empty boundary, arbitrary algebraically closed field and characteristic, and that no
projective or affine hypothesis appears. The only change from the returned material is the
new stage-2 module and its `lean` record, as required by H1/H2.

## Maintainer review fix (NT-cc reviewer, 2026-10-18)

The delivered geometric-fibre clause quantified over every algebraically closed field `Ω` in
universe `u` and every `g : Spec Ω ⟶ B'`. The node cites [def-weil-geometric-fibre], whose
geometric fibre over `y` is taken along `Spec` of the chosen algebraic closure of `κ(y)`. The
clause is now `∀ y : B', IsSemistableGeometricCurve (pullback.snd f' (geometricPoint B' y))`,
with `AlgebraicGeometry.Orgogozo.geometricPoint` from the module already imported. This is the
convention of `SemistableFactor.fibres` and of the only citer
`lem-trf-de-jong-geometrically-irreducible-tower`. The unused import
`Sheaf.AlgebraicGeometry.NodalGeometricFibres` was removed. Nothing else changed.
