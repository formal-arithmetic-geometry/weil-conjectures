## Worker report

The module `Sheaf.AlgebraicGeometry.CurveSmoothPolarizationCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_smooth_polarization_cover`, with its entire
proof postponed by `sorry`. It introduces no definitions and proves no theorem.

The source was read in `literature/stacks-project/moduli-curves.tex`: section-stack-curves,
lemma-polarized-curves-over-curves (Tag 0DQ0), the preceding definition of
PolarizedCurves, and the first proof paragraph of lemma-etale-locally-scheme (Tag 0E6F).
The last paragraph explicitly asserts the smooth surjective scheme cover and relative
polarization used here. The inherited Q96 merge in the ledger is a stage-1 split:
the current item has no Lean record or reviewed_lean and is queued at stage 2. There
is no released repair note. This delivery preserves its accepted natural-language
statement and proof, adding only its Lean record and two existing definition dependencies.

Hypothesis and clause correspondence:

* The scheme T is `T : Over S` and its underlying scheme is `T.left`.
  `X : AlgebraicSpace S` is the existing algebraic-space category and
  `f : X.obj.obj ⟶ yoneda.obj T` is the morphism to the scheme. The auxiliary
  ambient base S is arbitrary; choosing S = T.left and T = Over.mk (𝟙 S)
  includes every family in the node, so this adds no geometric hypothesis.
* `hf : IsProperCurveFamily X T f` is the recorded predicate in
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`, read in full. Its first conjunct
  is `MapToSchemeIsLocally (@Flat) X T f` (flatness on all representable etale
  scheme charts). Its next four conjuncts are `MapToSchemeIsSeparated`,
  `MapIsQuasiCompact f`, local finite type on etale charts, and
  `MapToSchemeIsUniversallyClosed`. These give precisely properness.
* Finite presentation is the same quasi-compactness conjunct, quasi-compactness of
  `pullback.diagonal f` (quasi-separatedness), and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`. Properness already
  implies quasi-separatedness, so spelling it out adds no assumption.
* The final conjunct of `hf` quantifies over `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  and every `a : Spec (.of Ω) ⟶ T.left`, and requires
  `topologicalKrullDim (Point (Limits.pullback f (yoneda.map ...))) ≤ 1`.
  These are the actual geometric fibres. The point topology is the existing
  final topology for etale scheme charts; its Krull dimension is equivalently the
  supremum of dimensions of affine etale charts. Empty fibres have dimension bottom.
* The new scheme and map are `U : Over S` and `p : U ⟶ T`.
  `Smooth p.left` is exactly smoothness, and `Surjective p.left` is surjectivity on
  underlying scheme points (every t has a point above it).
* `Y : Over S`, `q : Y ⟶ U`, and `a : yoneda.obj Y ⟶ X.obj.obj`, together with
  `IsPullback a (yoneda.map q) f (yoneda.map p)`, say that the scheme Y represents
  the algebraic-space fibre product X ×_T U. The projection q is tied to this
  fibre product by its universal property; it is not an arbitrary map.
* `L : Y.left.Modules` and `L.IsInvertible` give the ordinary invertible module on Y,
  using the existing scheme module category and invertibility class.
* `∀ W : U.left.Opens, IsAffineOpen W → ...` tests every affine open of U.
  The inverse image `(q.left ⁻¹ᵁ W).toScheme` is Y ×_U W, and
  `(Scheme.Modules.tensorPullback (q.left ⁻¹ᵁ W).ι).obj L` is its restriction.
  The existential `h` supplies the invertibility proof argument of the existing
  absolute `Scheme.Modules.IsAmple`; this is a property of this specific restriction,
  not a new module or added assumption. The last expression asserts exactly its ampleness.
* There are no Noetherian, connectedness, reducedness, nonempty-fibre or
  pure-dimension binders, and no implicit variables (`autoImplicit false`, universe u).

Dependency declarations used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  full-subcategory morphisms, and the representable chart convention.
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used by the family predicate.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (current
  spelling; the recorded `IsSmooth` name is a deprecated alias).
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, exposed by the ample module.
* `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, with exactly the node's absolute notion.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`; its full signature
  and docstring were read. It identifies sheaf fibre products with the algebraic-space
  products used in the node. The conclusion uses `IsPullback` to specify a scheme model.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.IsProperCurveFamily` and the constituent definitions
  listed above. Its already landed node `def-sfb-proper-curve-moduli` is added to
  stmt_deps instead of duplicating any family notion.
* `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the explicit sheaf tensor formula;
  its existing node `def-pc-module-pullback` is added to stmt_deps for the restriction.

The already stated proof dependencies are imported privately: the separated
one-dimensional-space scheme theorem, proper one-dimensional-scheme projectivity,
very-ample/ample field-extension lemmas, and the Zariski/etale quasi-coherent comparison.
The three unstated proof dependencies (Picard smoothness, proper/flat/fp locality,
and the relative ample locus) supply no objects needed to type this statement;
their proof steps remain fully described in the theorem docstring. The open-immersion
smooth-composition Mathlib match is already visible through the smoothness import.

Edge cases checked against the source and definitions: empty T allows empty U and Y,
with surjectivity vacuous; an empty fibre is allowed by dimension bottom, not forced to
be nonempty. Zero-dimensional and mixed zero/one-dimensional fibres satisfy ≤ 1.
Neither irreducibility nor reducedness nor characteristic is constrained. Arbitrary
schemes T, including non-Noetherian ones, are retained. All schemes and test fields
are in the existing big-site universe u, with no extra universe equality. Affine opens
include the empty open. The polarization is not required to be very ample, so the
conclusion has no unintended extra choice of a projective embedding.

Searches made before writing:

* `msearch.py ... leansearch "Proper flat curve families admit a relatively ample
  invertible sheaf after a smooth surjective scheme base change"`: 8 hits, concerning
  module flatness, scheme flatness and smooth base-change stability, no matching theorem.
* `msearch.py ... leanfinder "Proper flat finitely presented algebraic space curve
  families admit smooth surjective covers carrying a relatively ample invertible sheaf"`:
  8 hits, concerning scheme smoothness, universal openness and descent; no polarization theorem.
* `msearch.py ... loogle '"IsAmple", "IsSmooth"'`: 0 hits.
* `msearch.py ... grep 'PolarizedCurves|polarized.*curve|polarisation.*cover'`: 0 hits.
* `rg` of polarization spellings in `lean/WeilConjectures` and `lean/Sheaf` found
  other polarizations (abelian varieties and PGL) and the consumer CurveEtaleSchemeCover,
  but no smooth polarization cover theorem. Searching the exact item id in
  `lean/WeilConjectures` found no result. The consumer reuses the existing
  IsProperCurveFamily predicate, which this delivery also uses.
* `rg` of `IsProperCurveFamily` and `ProperCurveModuli` in `dag/nodes` and
  `lean/Sheaf` found `def-sfb-proper-curve-moduli`; the full record and source were read.
  `rg` of tensorPullback and the module-pullback node found the existing canonical
  construction, so no new helper definition or new node is introduced.

Validation: `scompile.py Q109 lem-sfb-curve-smooth-polarization-cover` compiled this
module separately against the published live library with no errors or warnings.
No statement dispute or source correction was needed. The previous worker's stage-1
already-merged refusal does not describe the current stage-2 statement assignment.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
