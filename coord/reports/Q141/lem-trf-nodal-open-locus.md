## Worker report

The module `Sheaf.TraceFormula.NodalOpenLocus` defines the auxiliary predicates
`AlgebraicGeometry.IsSmoothOrOrdinaryNode` and
`AlgebraicGeometry.HasOnlySmoothOrNodalGeometricFibres`, then states
`AlgebraicGeometry.nodalOpenLocus` with proof `sorry`.

The theorem binds schemes `Y,T`, a morphism `p : Y ⟶ T`, the hypotheses `[Flat p]` and
`[LocallyOfFinitePresentation p]`, and the hypothesis that every nonempty algebraically
closed geometric fibre is pure of dimension one. It asserts an open `U : Y.Opens`.
The first conjunct says every geometric fibre of `U.ι ≫ p` consists of smooth points or
closed ordinary nodes. The second says every open with this fibrewise property is contained
in `U`, rendering largestness. The third conjunct says that after every base change
`g : T' ⟶ T`, the inverse image of `U` has the same property and is largest among such
opens. The fourth gives the geometric-fibre pointwise description: over the chosen
`AlgebraicClosure (T.residueField t)`, membership in `U` is equivalent to being smooth or
an ordinary node. The final conjunct gives the stated criterion on the scheme-theoretic
fibre: all its points lie in `U` exactly when every singular point of the geometric fibre
satisfies the ordinary-node predicate.

`IsSmoothOrOrdinaryNode` renders the smooth clause as membership in
`f.smoothLocus`; its node clause requires a closed point and a ring isomorphism from the
maximal-ideal adic completion of the local stalk to
`MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`. The geometric-fibre predicate quantifies over
`Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]`, geometric points
`Spec (.of Ω) ⟶ T`, and points of the categorical pullback. The pure-dimension hypothesis
uses `Scheme.IsPureDimension` from the recorded dependency. Base-change fibres use
`pullback.fst`, `pullback.snd`, and inverse images of opens; the pointwise clauses use
`Scheme.fromSpecResidueField` followed by the canonical map to the algebraic closure.

Dependencies used: `AlgebraicGeometry.Flat` from
`Mathlib.AlgebraicGeometry.Morphisms.Flat`; `AlgebraicGeometry.Scheme` and categorical
`pullback` from Mathlib; `AlgebraicGeometry.LocallyOfFinitePresentation` from
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`;
`AlgebraicGeometry.Scheme.IsPureDimension` from
`Sheaf.AlgebraicGeometry.PureDimension`; `AlgebraicGeometry.Smooth` and
`Scheme.Hom.smoothLocus` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
`AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Algebra`; and
`MvPowerSeries` from `Mathlib.RingTheory.MvPowerSeries.Basic`.

Edge cases checked: the pure-dimension premise is conditional on nonempty fibres, so
empty fibres are admitted; `Fin 2` gives exactly two node variables; the construction
allows arbitrary characteristics (including characteristic two); the open `U` may be
empty; and the base-change quantifier includes the identity and empty-open cases.

Searches made before writing: `msearch.py ... leanfinder` for a maximal nodal open,
`msearch.py ... loogle` for smooth/étale/open-locus names, and Mathlib grep for
`nodal|semistable|ordinary.double.point|semistability`; these found only generic smooth,
unramified, and Lagrange-polynomial declarations and no nodal-open statement. `rg` over
`WeilConjectures/` and project `lean/Sheaf` found no existing declaration of this item.
The dependency declarations and their full signatures were read from the recorded modules
and Mathlib source.

No statement correction, dependency module, or new definition node was needed.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
