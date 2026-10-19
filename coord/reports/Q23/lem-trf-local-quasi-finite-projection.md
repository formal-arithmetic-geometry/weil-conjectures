## Worker report

The module `Sheaf.TraceFormula.LocalQuasiFiniteProjection` states
`AlgebraicGeometry.localQuasiFiniteProjection` with one postponed proof. It uses the
existing scheme, finite-type, geometric-point, fibre, Krull-dimension, relative affine
space, separatedness, and quasi-finite notions from the recorded dependencies.

The Lean statement renders the node clause by clause as follows. The affine base is the
binder `{B Y : Scheme.{u}} [IsAffine B]`. The locally finite type morphism is
`(g : Y ⟶ B) [LocallyOfFiniteType g]`. The geometric point is
`(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` together with
`(y : Spec (.of Ω) ⟶ Y)`; its image point is `y (closedPoint Ω)`, using the unique
closed point of the spectrum of an algebraically closed field. The nonnegative integer
bound is `(N : ℕ)` and the fibre hypothesis is
`(hN : ∀ s : B, topologicalKrullDim (g.fiber s) ≤ (N : WithBot ℕ∞))`.

The conclusion is `∃ U : Y.Opens, IsAffineOpen U ∧ y (closedPoint Ω) ∈ U ∧ ...`,
so `U` is an affine open neighbourhood of the image point. It then has
`∃ d : ℕ, d ≤ N ∧ ...`; the lower bound `0 ≤ d` in the source is represented by the
natural-number binder itself, avoiding a tautological proposition. The projection is
`e : U.toScheme ⟶ 𝔸(ULift.{u} (Fin d); B)`, where the `ULift` is required by
Mathlib's universe-indexed `AffineSpace`. Its separated clause is `IsSeparated e`,
and its quasi-finite clause is the project's Stacks predicate
`Scheme.Hom.IsQuasiFinite e`, which includes finite type and isolated (hence finite
discrete on affine fibres) fibre points. Finally,
`e ≫ (𝔸(ULift.{u} (Fin d); B) ↘ B) = U.ι ≫ g` is exactly the structural composite
condition expressing `g|_U`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (and its finite-type API).
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and
  `Mathlib.AlgebraicGeometry.ResidueField`: `IsAlgClosed`,
  `AlgebraicGeometry.Scheme.SpecToEquivOfField`; the latter's signature identifies
  `Spec (.of Ω) ⟶ Y` with a point and a residue-field map.
- `Mathlib.AlgebraicGeometry.Fiber`:
  `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and the
  notation `𝔸(n; S)`; the finite-dimensional index is
  `ULift.{u} (Fin d)`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated`. The recorded `def-weil-proper-morphism` node
  defines properness together with separatedness; this statement uses the explicitly
  requested separated subclause, not the stronger `IsProper` predicate.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`, the recorded realization of
  `pqf-def-quasifinite`.

Edge cases checked before writing: `N = 0` permits `d = 0`; `d = 0` is represented by
`Fin 0` and Mathlib's `AffineSpace (ULift.{u} (Fin 0))`; the lower bound on `d` is
automatic for `d : ℕ`; empty fibres are allowed by the `WithBot ℕ∞` Krull-dimension
bound; and the image point uses `closedPoint Ω`, which is the unique point of
`Spec Ω` for algebraically closed `Ω`. No extra noetherian, separatedness of `g`, or
nonempty-fibre hypothesis was added.

Searches for an existing declaration were run as follows. `msearch.py ... leanfinder
"local quasi finite projection affine space bounded fibre dimension"` returned generic
`LocallyQuasiFinite`, `LocallyOfFiniteType`, affine-space, and separatedness declarations,
but no bounded-dimension projection theorem. A second LeanFinder phrasing about a
locally finite-type morphism with bounded fibres likewise returned only generic
quasi-finite and affine-space APIs. `msearch.py ... loogle
"LocallyQuasiFinite AffineSpace topologicalKrullDim"` reported no result (unknown
identifier). A Mathlib grep for `quasiFinite.*projection|localQuasiFinite.*AffineSpace`
returned zero hits. The corresponding source-tree grep for
`quasiFiniteProjection|localQuasiFiniteProjection|bounded.*dimension` returned only
unrelated bounded-dimension/cohomology prose and no declaration. `rg` over the existing
`lean/Sheaf` and `WeilConjectures` trees found no declaration with this name or the
statement. The full DAG search found only this node and its reviewed parent split.

The prior Q56 stage-1 split was read in full. It confirms that the item remains the
three-step scheme-level statement and that the affine weak relative Noether-normalization
lemma is a proof dependency of the parent, not an additional statement dependency here.
The Orgogozo PDF named by the source record is still unavailable locally; this does not
change the Lean statement, which follows the recorded source wording and the reviewed
Stacks translation.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
