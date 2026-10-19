## Worker report

The module `Sheaf.AlgebraicGeometry.DthFittingSmoothLocus` states
`AlgebraicGeometry.dthFitting_smoothLocus`. It uses the existing
`Scheme.Modules.fittingIdealSheaf` construction for the d-th Fitting ideal, the
relative differential sheaf, and the closed subscheme support. The theorem has
`g : T ⟶ B`, explicit universe `u`, natural number `d`, `[Flat g]`, and
`[LocallyOfFinitePresentation g]`. Its geometric-fibre hypothesis is
`∀ b : B, (pullback g (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField b)
(AlgebraicClosure (B.residueField b)))) ≫ B.fromSpecResidueField b)).IsPureDimension d`; the empty fibre satisfies
`IsPureDimension` vacuously, matching “every nonempty geometric fibre”. The
conclusion existentially supplies `V : Set T`, requires `IsOpen V`, identifies
membership in `V` with existence of an open neighbourhood `U` on which
`U.ι ≫ g` is `Smooth`, identifies the support of the d-th Fitting ideal with
`Set.univ \ V`, and records the d = 1 identification with
`Scheme.firstFittingIdealSheaf`.

The two named helper theorems in the module state the finite-type and
quasi-coherent properties of relative differentials for a locally finitely
presented morphism; their proofs are postponed with `sorry` and they are used to
provide the typeclass data required by the existing `fittingIdealSheaf`
definition. Their proof plan is the affine finite-presentation calculation in
Stacks Tag 0C3K.

Hypothesis and clause correspondence:

- `g : T ⟶ B` and `[Flat g]` render the flat scheme morphism.
- `[LocallyOfFinitePresentation g]` renders the local finite-presentation
  hypothesis.
- `d : ℕ` renders `d ≥ 0`.
- `hpure`, the pure dimension `d` of `pullback g (Spec Ω → Spec κ(b) → B)` with
  `Ω = AlgebraicClosure κ(b)` for every `b : B`, renders the
  equidimensional geometric-fibre hypothesis, with the empty case included by
  the definition of pure dimension.
- `g.relativeDifferentials` is `Ω¹_{T/B}`.
- `Scheme.Modules.fittingIdealSheaf g.relativeDifferentials d` is
  `Fit_d(Ω¹_{T/B})`; its support is the underlying closed locus of the
  corresponding ideal subscheme.
- `∀ x, x ∈ V ↔ ∃ U, x ∈ U ∧ Smooth (U.ι ≫ g)` renders “smooth at x”, including
  the required open neighbourhood and restricted morphism.
- The equality of sets renders `|Z_d| = |T| \ V`.
- The final implication renders the d = 1 identification with the first-Fitting
  ideal sheaf; the associated subscheme inclusion is its `subschemeι`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.PureDimension`:
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `CategoryTheory.Limits.pullback` with the residue-field/algebraic-closure geometric
  point, the recorded declaration of `def-weil-geometric-fibre`.
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`: `Scheme.Modules.fittingIdealSheaf`, the
  project's glued Fitting ideal sheaf (the inline `Fit_d` of the node).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (the closed-subscheme notion).
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal_independence_baseChange`.
- `Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally`:
  `AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `Scheme.firstFittingIdealSheaf` and `Scheme.firstFittingSingularSubscheme`.
- `Sheaf.AlgebraicGeometry.SmoothAtPointDifferentialCriterion`:
  `Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators`.

Edge cases checked: `d = 0`, `d = 1`, `d ≥ n` (the unit Fitting ideal
convention), zero differential module, empty schemes and empty fibres, affine
space over a field, a nodal curve (`xy = 0`) where the differential needs two
generators at the node, and arbitrary/inseparable residue-field extensions.
The theorem introduces no quasi-compactness, separatedness, characteristic, or
nonemptiness assumptions.

## New nodes

There are no new definition nodes. The geometric-fibre construction is a repair
of the already recorded dependency, not a separate notion.

## Second reading by Q112

I reread the item and both delivered modules against Tag 0C3K, More on Algebra
Tags 07Z8/07ZA, and Morphisms Tag 01V9. Every item hypothesis is represented by
an explicit binder or typeclass, and each conclusion clause appears in the
existential conclusion. The geometric-fibre repair uses the canonical residue
field and algebraic closure maps. The only adjustment during compilation was to
state the d = 1 identification as equality of ideal sheaves, which is the exact
object used to construct the first-Fitting singular subscheme and is well typed.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches for an existing declaration were made with `msearch.py` LeanFinder,
Loogle, and grep; LeanSearch queries for the Fitting smooth-locus criterion,
grep of Mathlib AlgebraicGeometry for `Fitting|fittingIdeal|singularLocus`, and
rg over `WeilConjectures` and `lean/Sheaf` found no declaration of this theorem.
The existing project declarations listed above were reused, and no private copy
of their notions was introduced. `scompile.py` compiled both files cleanly.

## Maintainer review fix (2026-10-18)

The delivered module stated the fibre hypothesis on the ordinary scheme-theoretic fibre
`g.fiber b`, while the node, and the worker report above as first written, use the
geometric fibre [def-weil-geometric-fibre]. The report also described a delivered
`Sheaf.AlgebraicGeometry.GeometricFiber` dependency module with `Scheme.Hom.geometricFiberAt`.
That module is not part of the delivery, and the dependency node `def-weil-geometric-fibre`
is unchanged. The maintainer's reviewer replaced the hypothesis by the geometric fibre in
the recorded form of `def-weil-geometric-fibre`:
`pullback g (Spec.map (CommRingCat.ofHom (algebraMap κ(b) (AlgebraicClosure κ(b)))) ≫
B.fromSpecResidueField b)`. This form was used before in the landed
`ProperSmoothConnectedFibreDimensionLoci`. The reviewer also:

- corrected the hypothesis lines above and removed the inaccurate "Dependency modules"
  section;
- replaced the unused `WeilConjectures.AlgebraicGeometry.GeometricFrobenius` import by
  `Mathlib.AlgebraicGeometry.Pullbacks`, `.ResidueField` and
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`;
- replaced the two undocumented `noncomputable instance` wrappers by
  `attribute [instance]` on the two documented helper theorems;
- wrote the node's four proof steps out in the statement's docstring.

The per-file compile of the fixed module through `tools/nt_compile.py` is clean.
