## Worker report

The module defines the statement `Algebra.SubmersivePresentation.topologicalKrullDimAt_spec_eq`.
It uses Mathlib's `Algebra.SubmersivePresentation`, with `Fin n` variables and `Fin c` relations;
`hnc : c ≤ n` records the required inequality and `hmap : P.map = Fin.castLE hnc` says that the
Jacobian minor uses the first `c` variables. `P` is a presentation over a field `k` of a
commutative `k`-algebra `B`, and `Q : PrimeSpectrum B` is an arbitrary prime. The conclusion is
that `topologicalKrullDimAt` of `Spec B` at `Q` equals `n - c` (coerced to `WithBot ℕ∞`). The proof
is `sorry`, as required for stage 2.

The Lean binders render each clause as follows: `[Field k]`, `[CommRing B]`, and `[Algebra k B]`
render the field and algebra hypotheses; `hnc : c ≤ n` renders `n ≥ c ≥ 0`; `P` renders the
standard smooth presentation data (finite variable/relation types and invertible Jacobian from
`SubmersivePresentation`); `hmap` identifies the Jacobian variable injection with the first `c`
variables; `Q : PrimeSpectrum B` renders an arbitrary prime ideal; and the equality renders
`dim_Q (Spec B) = n-c` via `topologicalKrullDimAt`.

Dependency declarations used: `Algebra.SubmersivePresentation` from
`Mathlib.RingTheory.Extension.Presentation.Submersive`; `AlgebraicGeometry.Spec` from
`Mathlib.AlgebraicGeometry.Scheme`; and `topologicalKrullDimAt` from
`WeilConjectures.Mathlib.Topology.KrullDimension`.

Edge cases checked: `c = 0`, `c = n`, and arbitrary `Q`; `Fin 0` correctly represents an empty
relation or variable index, and `hnc` prevents `c > n`. No nontriviality or nonempty-spectrum
hypothesis is added.

Searches made: `msearch.py ... leanfinder` for “standard smooth presentation over a field ...
dimension n minus c at every point” returned only relative-dimension declarations, with no
pointwise dimension theorem; `msearch.py ... loogle` for
`Algebra.SubmersivePresentation, topologicalKrullDimAt` found no match for the project-only name;
`msearch.py ... grep` for `topologicalKrullDimAt|equidimensional|krullDim` in smooth files found
no theorem; `rg` over `WeilConjectures` and `lean/Sheaf` found no existing declaration of this
node. The Stacks source was checked at Tags 00T6 and 00T7.

## Second reading by Q1

I independently compared the node statement with
`Sheaf/RingTheory/StandardSmoothDimensionAtPoints.lean` and with the dependency
records. The objects and hypotheses render as follows:

- A field `k` is `{k : Type u} [Field k]`.
- A commutative `k`-algebra `B` is `{B : Type v} [CommRing B] [Algebra k B]`.
- The integers `n ≥ c ≥ 0` are `{n c : ℕ}` and `hnc : c ≤ n`.
- The standard smooth presentation is
  `P : Algebra.SubmersivePresentation k B (Fin n) (Fin c)`; its finite variable
  and relation indices, quotient presentation, and invertible Jacobian are the
  Mathlib presentation structure recorded by `def-weil-pbc-standard-smooth-algebra`.
  `hmap : P.map = Fin.castLE hnc` selects the first `c` variables, matching the
  node's ordering convention for the Jacobian minor.
- An arbitrary prime ideal is `Q : PrimeSpectrum B`.
- The conclusion is exactly
  `topologicalKrullDimAt (X := AlgebraicGeometry.Spec (CommRingCat.of B)) Q =
  (n - c : ℕ)`, using the recorded `topologicalKrullDimAt` notion for the
  dimension at a point and Mathlib's `Spec`.

The Lean signature has no extra Noetherian, finite type, nonempty spectrum,
separation, characteristic, or universe restriction, and no hypothesis from the
source is omitted. The Mathlib presentation is the dependency's recorded
specialization of the explicit polynomial presentation (with `Fin n`, `Fin c`
and the map condition), so no alternate private notion was introduced. The
proof remains `sorry` as required at stage 2, and the declaration docstring
contains the node proof steps and all cited dependencies.

Edge cases checked: `c = 0` and `n = c` are represented by `Fin 0` and give the
expected empty-Jacobian and zero-relative-dimension cases; `hnc` excludes
`c > n`; `Q` is arbitrary, including every prime when the spectrum is empty
(vacuously); no nontriviality or characteristic assumption is present. The
universe levels are tied only to `k` and `B`, while the finite indices are
`Fin n` and `Fin c`, so no case is excluded.

I repeated the existing-definition searches with LeanFinder/Loogle and grep over
Mathlib, `WeilConjectures`, and `lean/Sheaf`. They found only the generic
`Algebra.SubmersivePresentation`/relative-dimension declarations and the
recorded `topologicalKrullDimAt`; no theorem with this pointwise dimension
statement exists. Thus the module is needed and no dependency module or node
correction is required. The module compiled cleanly with `scompile.py`; no
mismatch was found and no source or node statement was changed.
