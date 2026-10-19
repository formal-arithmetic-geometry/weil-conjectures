## Worker report

The module `Sheaf.AlgebraicGeometry.CompositeFibreDimensionInequality` states
`AlgebraicGeometry.composite_fibre_dimension_at_point_le`, with its entire proof
postponed as `sorry`. The statement is the first assertion of Stacks Tag 02JS
(`literature/stacks-project/morphisms.tex`, lemma-dimension-fibre-at-a-point-additive,
lines 5396–5404). I read the source statement and its proof. No node correction,
new notion, or dependency repair is needed.

Hypothesis and clause correspondence:

- Schemes X, Y, T: `{X Y T : Scheme.{u}}`, with the explicit arbitrary universe `u`.
- Morphisms f:X→Y and g:Y→T: `(f : X ⟶ Y) (g : Y ⟶ T)`.
- Both locally of finite type: `[LocallyOfFiniteType f] [LocallyOfFiniteType g]`.
  There is no global finite-type or quasi-compactness assumption.
- An arbitrary point x of X: `(x : X)`.
- y=f(x) and t=g(y) are substituted directly, with no local definitions or extra binders.
- The composite is `f ≫ g`. Its fibre at t and its point over x are respectively
  `(f ≫ g).fiber ((f ≫ g) x)` and `(f ≫ g).asFiber x`.
- The fibre X_y and its point are `f.fiber (f x)` and `f.asFiber x`.
- The fibre Y_t and its point are `g.fiber (g (f x))` and `g.asFiber (f x)`.
- Each local topological dimension is the recorded `topologicalKrullDimAt` applied
  to the indicated fibre point. The displayed conclusion is exactly
  `topologicalKrullDimAt ((f ≫ g).asFiber x) ≤
  topologicalKrullDimAt (f.asFiber x) + topologicalKrullDimAt (g.asFiber (f x))`.
  Both addition and order are those on `WithBot ℕ∞` used by the dimension definition.
- No flatness hypothesis is present. The source's additional equality under flatness
  is outside this node, and is already separately stated by the flat-composite node.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, declarations
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, and `fiberToSpecResidueField`.
  The same module's `Scheme.Hom.asFiber` uses the inverse fibre homeomorphism
  to select the canonical point above x; it is not an arbitrary fibre point.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  declaration `AlgebraicGeometry.LocallyOfFiniteType`. Its other recorded notion,
  `QuasiCompact`, is not a hypothesis of this node.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`, the
  infimum over open neighbourhoods of the topological Krull dimension.

Proof dependencies are imported non-publicly where they are not already public
statement dependencies: `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula`
(`AlgebraicGeometry.topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg`),
`Sheaf.AlgebraicGeometry.CompositeFibreLocalModels`
(`AlgebraicGeometry.composite_fibre_local_models`),
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis` (`Algebra.trdeg_add_eq`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_le_height_add_of_liesOver`), `Mathlib.AlgebraicGeometry.Pullbacks`
(`AlgebraicGeometry.pullbackSpecIso`), and `Mathlib.AlgebraicGeometry.Noetherian`
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`).
`IsOpen.topologicalKrullDimAt_eq` is supplied by the public dimension module.
The docstring records all four proof steps and their DAG identifiers, including
application of the finite-type dimension formula on affine neighbourhoods, so its
quasi-compactness requirement does not impose a global hypothesis here.

Edge cases checked before drafting:

- Empty X: there is no x; the universally quantified conclusion is vacuous.
  More generally the three fibres in this statement cannot be empty because
  the canonical points are supplied by x and f(x).
- Identity morphisms: the corresponding point fibre has dimension zero, reducing
  the formula to equality. Zero-dimensional fibres are allowed.
- Non-flat closed inclusion `Spec k → A¹_k` followed by `A¹_k → Spec k`:
  the formula reads `0 ≤ 0 + 1`; the inequality may be strict, so neither equality
  nor a flatness hypothesis has been substituted.
- Locally finite type, non-quasi-compact schemes are allowed: all necessary
  finite-type reductions occur only in the proof's affine neighbourhoods.
- Generic/nonclosed points and nonreduced schemes are included: `asFiber` has no
  closedness premise and `topologicalKrullDimAt` is topological local dimension,
  rather than stalk dimension. No base field, characteristic, or Noetherian-base
  hypothesis occurs. One arbitrary scheme universe follows the Mathlib category.

Searches for an existing declaration:

- `msearch.py` leanfinder, query "dimension at a point of the fibre of a composite
  of locally finite type scheme morphisms is at most sum of successive fibre
  dimensions": 8 hits concerning local finite type composition and finite
  morphisms, no dimension inequality.
- `msearch.py` loogle, query
  `topologicalKrullDimAt, AlgebraicGeometry.Scheme.Hom.fiber`: no hits; the service
  does not know the upstream-only identifier `topologicalKrullDimAt`.
- `msearch.py` grep, query
  `topologicalKrullDimAt|dimension.*fibre.*add|fiber.*dimension.*add`, subdirectory
  `AlgebraicGeometry`: no Mathlib hits.
- `msearch.py` leansearch, query "local dimension of a composite scheme fibre is
  at most the sum of the local dimensions of the successive fibres": 8 hits,
  including smooth relative-dimension composition and presentation dimensions,
  no matching theorem.
- `rg -n 'topologicalKrullDimAt|lem-trf-composite-fibre-dimension-inequality'`
  in `WeilConjectures` and `lean/Sheaf`: the existing topology definition,
  finite-type dimension formula and other special cases; no matching inequality.
  In particular I opened `FlatCompositeFibreDimensionAtPoint.lean`: its equality
  requires flatness at the point and cannot state this unrestricted inequality.
- `grep -rn 'lem-trf-composite-fibre-dimension-inequality'` in `WeilConjectures`:
  no hits. Targeted `rg` in `dag/lean_names_upstream.json` and both source roots
  found no existing composite inequality or declaration with the chosen name
  `composite_fibre_dimension_at_point_le`.

No statement dispute or node fault was found. All writes are in the assigned
sandbox; compilation and delivery use the authorized wrappers only.

Validation: `scompile.py Q42 lem-trf-composite-fibre-dimension-inequality` compiled
this module successfully against the published library and side overlay, with
no errors or warnings (sandbox check 16.7 s; library module check 3.5 s).

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
