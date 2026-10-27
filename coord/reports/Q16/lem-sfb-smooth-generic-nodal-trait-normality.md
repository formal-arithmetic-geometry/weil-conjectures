## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGenericNodalTraitNormality` states
`AlgebraicGeometry.normal_dense_integral_of_smooth_generic_nodal_trait`, with a
single `sorry` and the seven complete DAG proof steps in its docstring. No
construction or proof is added. The mathematical statement is unchanged. The
item's `stmt_deps` gains the already landed
`def-sfb-nodal-geometric-fibre-local-rings`, as permitted by the landed-node rule,
to use its actual completion, split-node quotient and canonical projection.

Hypothesis and conclusion correspondence:

- The DVR A is `A : CommRingCat.{u}`, `[IsDomain A]` and
  `[IsDiscreteValuationRing A]`. The base T is written directly as `Spec A`.
  The fraction field is `F : Type u`, `[Field F]`, `[Algebra A F]` and
  `[IsFractionRing A F]`. Uniformizers and residue fields are canonical
  notions available from the DVR instance and are not additional hypotheses.
- The given map is `{X : Scheme.{u}} (f : X ⟶ Spec A)`.
  Flatness is `[Flat f]`; finite presentation is exactly
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
  No separatedness, projectivity or properness is assumed.
- `hgeneric` says that the second projection of the pullback along
  `Spec.map (CommRingCat.ofHom (algebraMap A F))` is smooth: smoothness of X_F over F.
- `hfibres` quantifies over every algebraically closed field `Ω : Type u` and
  every geometric point `g : Spec (.of Ω) ⟶ Spec A`. Each fibre is the actual
  categorical pullback. `IsReduced` and `.IsPureDimension 1` express the first
  two fibre conditions and allow empty fibres. For each closed point z, negated
  formal smoothness of the stalk map is exactly nonsmoothness (the definition of
  Mathlib's smooth locus for locally finitely presented maps). The final clause
  is the required completed-stalk isomorphism to the split-node quotient.
- The first conclusion universally asserts both `IsDomain` and
  `IsIntegrallyClosed` for each stalk, preserving disconnected X.
- `DenseRange (pullback.fst f (Spec.map ...))` is density of the generic-fibre
  open in X. The final implication is generic-fibre integrality implying
  `IsIntegral X`; no connectedness or projectivity is assumed.

Dependency declarations read and reused:

| Node | Module | Declaration |
| --- | --- | --- |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic | IsDiscreteValuationRing |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec; Spec.map |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| def-weil-geometric-fibre | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsReduced |
| def-weil-pure-dimension | Sheaf.AlgebraicGeometry.PureDimension | AlgebraicGeometry.Scheme.IsPureDimension |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic | AdicCompletion |
| def-weil-pbc-multivariate-power-series | Mathlib.RingTheory.MvPowerSeries.Basic | MvPowerSeries |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-sfb-nodal-geometric-fibre-local-rings | Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings | AlgebraicGeometry.NodalFiber.* |

The proof plan imports all stated proof dependencies with plain `import` where
available. The nodal-trait-finite-singular-charts dependency has no Lean record
yet and is retained unchanged in the proof plan.

Edge cases checked: empty X and empty fibres, disconnected smooth-family unions,
uv=π^n for n=1 and n>1, uv=0 excluded by generic smoothness, arbitrary residue
characteristic, and nonexcellent DVRs. The same universe `u` is used for rings,
schemes and geometric fields, avoiding a vacuous smaller test universe.

Searches (msearch.py, 2026-10-24): LeanFinder found only Weierstrass and
normalization results; Loogle `"IsIntegrallyClosed", "Flat"` found zero; Mathlib
grep `nodal|semistable|normal.*trait` in AlgebraicGeometry found zero; LeanSearch
found only smooth algebra flatness and generic reduction results. `rg` over
lean/WeilConjectures and lean/Sheaf found related normalization/semistable results
with different hypotheses, but no duplicate theorem. Existing
NodalGeometricFibreLocalRings was read and reused.

There is no statement correction, new definition, unusable dependency, or
STATEMENT-DISPUTED flag. `scompile.py` compiled the module cleanly. The initial
smoothLocus spelling required an unavailable finite-presentation instance for the
opaque helper projection; the exact stalk-map formal-smoothness condition fixed
elaboration without changing the mathematics.

## Second reading by Q16

I re-read the node and final signature clause by clause after compilation:
DVR and fraction field, flatness and finite presentation, smooth generic fibre,
all geometric-fibre hypotheses, closed nonsmooth points and completed-node rings,
all-stalk normal domains, generic-fibre density, and conditional integrality are
all present. No projectivity, properness or connectedness was added. The only
edit after the first compile was the definitionally equivalent smoothness
condition noted above. No mismatch remains.
