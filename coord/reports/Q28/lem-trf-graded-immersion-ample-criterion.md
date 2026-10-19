## Worker report

The delivery adds `Sheaf.TraceFormula.GradedImmersionAmpleCriterion`.  It states the
Stacks Project Tag 01VJ implication (6) implies (1) for an arbitrary quasi-coherent
graded algebra on `S` and an invertible module on `Z`; the algebra is allowed to have
an arbitrary degree-zero part and to require generators in arbitrary positive degrees.
The module records the affine-open form of the graded map, its canonical chart map,
and the generation locus so that the theorem has the exact hypotheses `U(ψ) = Z` and
`r_{L,ψ}` an immersion.

`RelativeGradedLineMap` is the explicit graded map datum.  For every affine open `V`
of `S` and degree `n`, `component V n` maps the graded piece `A.grading V n` to
sections of `L.tensorPow n` on `h ⁻¹ᵁ V`; `smul` is the `Γ(S,V)`-linearity condition,
`one` is the degree-zero unit, `mul` is the tensor-product multiplication condition,
and `restriction` is compatibility with affine-open restriction.  No degree-one
condition or equality `A_0 = O_S` is imposed.

`RelativeGradedLineMap.evaluate` is the canonical section on a scheme chart: it uses
the normalized tensor-pullback adjunction and `boundaryPullbackPowIso` to pull a
component section to the chart.  `GeneratesEverywhere` says that for each point of
`Z` there is an affine base neighbourhood, a positive degree, and a homogeneous
component whose germ is outside the maximal-ideal submodule; this is exactly the
union of positive-degree surjectivity loci being all of `Z`.  `IsCanonicalMap` first
requires `r ≫ A.relProjHom = h`, then imposes the homogeneous-fraction formula on
every open-immersion chart and every irrelevant-ideal witness, using
`Proj.fromOfGlobalSections` and `A.relProjι`.

The theorem `graded_immersion_ample_criterion` binds `h : Z ⟶ S` with
`[QuasiCompact h]`, `L : Z.Modules` with `[L.IsInvertible]`, arbitrary
`A : S.GradedAlgebraData`, the graded map `ψ`, the everywhere-generation hypothesis,
a canonical map `r : Z ⟶ A.relProj`, its canonical-map property, and
`[IsImmersion r]`.  Its conclusion is, for every affine open `V ⊆ S`, existence of
the inherited invertibility instance on the tensor pullback of `L` to `h ⁻¹ᵁ V` and
`Scheme.Modules.IsAmple` for that restriction.  This renders every hypothesis and
clause of the node statement without adding a degree-one, finite-generation, or
`A_0 = O_S` assumption.

Dependency declarations used:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` (Mathlib), with morphisms `Scheme.Hom`.
* `def-weil-finite-type-morphism`: `AlgebraicGeometry.QuasiCompact` (Mathlib).
* `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
* `def-weil-pbc-quasi-coherent-algebra`: `AlgebraicGeometry.QuasiCoherentAlgebra`
  and its affine-basis use `Scheme.GradedAlgebraData` from
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra` and
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`.
* `def-weil-pbc-graded-sheaf-structures`: the graded algebra interface represented by
  `Scheme.GradedAlgebraData`, imported from
  `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`/relative-Proj data.
* `def-pc-module-pullback`: `Scheme.Modules.tensorPullback` and its normalized
  section adjunction from `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.
* `def-pur-sheaf-tensor-product`: the module tensor structure and `tensorPow`/
  `tensorPowAddIso` used by `RelativeGradedLineMap`.
* `lem-trf-space-line-module-proj-map`: the canonical Proj chart conventions,
  `AlgebraicSpace.trivializedPower`, and `Proj.fromOfGlobalSections` imported from
  `Sheaf.TraceFormula.SpaceLineModuleProjMap`.
* `def-nagata-relative-proj`: `Scheme.GradedAlgebraData.relProj`, `relProjHom`, and
  `relProjι` from `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`.
* `def-weil-closed-immersion`: `AlgebraicGeometry.IsImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion` (the node's stated immersion notion).
* `def-weil-pbc-ample-invertible-module`: `Scheme.Modules.IsAmple` from
  `WeilConjectures.AlgebraicGeometry.Ample`.

Edge cases checked: the structure permits an empty affine-open index and empty
positive-degree pieces; `GeneratesEverywhere` is then vacuous exactly for the empty
scheme.  Degree zero is handled by the explicit unit law, while generation requires
`0 < n`, so degree-zero sections alone do not satisfy the hypothesis.  Tensor powers
include degree `0`; pullback to an empty inverse image is allowed.  No universe
restriction beyond the common scheme universe is introduced, and arbitrary positive
degrees (including non-degree-one gradings) are allowed.  The proof docstring records
the non-degree-one Proj twist issue and restricts the tensor-power comparison to the
quasi-compact open where it is valid.

Searches made: `msearch.py Q28 ... leanfinder` for “quasi compact scheme with an
immersion into relative Proj ... ample” and “invertible module ... canonical morphism
into Proj ... immersion”; both returned only Proj/chart declarations and no criterion.
`msearch.py ... loogle "ample, Proj"` and `"IsAmple, IsImmersion, Proj"` returned
no hits.  `msearch.py ... grep "characterize.relatively.ample|ample.*Proj|..."`
found no Mathlib criterion.  `msearch.py ... leansearch` for graded-algebra canonical
Proj maps found only `Proj`, `awayι`, and chart declarations.  `rg` over the project
found the related canonical-map and scheme criterion modules; their recorded
interfaces were read and the arbitrary-map interface was stated here rather than
silently specializing to the canonical section algebra.  No exact existing
`graded_immersion_ample_criterion` declaration was found.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
