## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedImmersionUnramifiedCriterion`
states `AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_iff_unramified_universallyInjective`.
Its single theorem has proof `sorry`. There are no new definitions or dependency repairs.
The node is unchanged outside `lean`.

I read the node, each statement dependency and its recorded declaration, the current
algebraic-space, point-class, point-topology, morphism-property and scheme-unramified
interfaces, and the node's four proof steps. The source was checked both in
`literature/stacks-project/spaces-more-morphisms.tex`, lemma-characterize-closed-immersion,
and at [Stacks Tag 05W8](https://stacks.math.columbia.edu/tag/05W8).
The theorem is precisely (1) equivalent to (3), with universal closedness fixed.

Clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}` |
| Algebraic spaces X,Y over S | `{X Y : AlgebraicSpace S}` |
| The fixed size convention | Explicit `universe u`, `Scheme.{u}`, and the recorded universe-polymorphic `AlgebraicSpace S`; point classes are the existing `Point : Type (u + 1)` |
| A morphism g:X to Y | `(g : X ⟶ Y)` in the full subcategory of fppf sheaves |
| g universally closed on point spaces after every algebraic-space base change | `(hg : MapIsUniversallyClosed g)`; this definition quantifies over every `Y' : AlgebraicSpace S` and map to Y and applies `IsClosedMap` to `mapPoint` of the sheaf pullback's second projection |
| g is a closed immersion, meaning representable with every scheme base change a closed immersion | `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) g.hom.hom`; its definition supplies a scheme, its projection and a representing pullback square for every scheme test |
| If and only if | `↔` |
| g unramified, in the stated chart sense | `MapIsLocally (@IsUnramified) g`; `MapIsLocally` quantifies over all compatible representable etale scheme charts, and `IsUnramified` is exactly local finite type and open-immersion diagonal |
| And universally injective | The conjunction followed by `∀ (Y' : AlgebraicSpace S) (h : Y' ⟶ Y), Function.Injective (mapPoint (pullback.snd g.hom h.hom).hom)` |
| Sheaf fibre products and existing point spaces | `pullback.snd g.hom h.hom` is the sheaf pullback projection, and the existing `mapPoint` uses `Point`, with its recorded final topology used by universal closedness |

The sentence about local finite type describes a notion used inside unramifiedness;
it is not an additional finite-type hypothesis. The theorem adds no representability
hypothesis: representability belongs to the left side and is a consequence on the right.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. These ensure that the sheaf pullbacks in the statement
  are the required algebraic spaces and provide the chart pullback in the proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, `PointRepresentative.map`, `pointImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`, `MapIsUniversallyClosed`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli` (publicly imported by the preceding module):
  `AlgebraicSpace.mapPoint`; this uses the existing point classes rather than a copy.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention and
  has no declaration or module; no extra object or artificial size hypothesis is added.

All statement-dependency modules with recorded modules are directly publicly imported.
For stated proof-only dependencies the file imports
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` (`Point`, `PointRepresentative.Rel`,
`schemePointMap`) and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`
(`UniversallyInjective`, `tfae_universallyInjective`). The four proof-only nodes
`lem-sfb-universally-closed-unramified-radicial-criterion`,
`lem-sfb-unramified-etale-compatible-charts`,
`lem-sfb-space-unramified-radicial-representable`, and
`lem-sfb-space-unramified-permanence` currently have no Lean binding; there is no module
to import for these. They are not needed to type the statement. The theorem's docstring
contains all four natural-language proof steps, naming these inputs for stage 3.

Edge cases checked before writing:

- Empty source: all pullback point maps have empty domain and are injective; empty closed
  immersions and the chart test remain included. Empty target and empty base are included
  without `Nonempty` binders. All test schemes and spaces, including empty ones, remain
  quantified.
- Identity and arbitrary isomorphisms: universally closed, unramified and universally
  injective, and closed immersions. The universal quantifier includes identity base change.
- A disjoint double copy of a nonempty scheme over itself is finite etale and universally
  closed but fails universal injectivity, as it must.
- A nontrivial finite purely inseparable field extension is universally closed and
  universally injective but not unramified, so the unramified conjunct is essential.
- A nontrivial finite separable extension is universally closed and unramified, but becomes
  noninjective after a splitting-field base change. Hence injectivity on the original
  point space alone would be insufficient; the Lean statement retains every base change.
- A nonclosed open immersion is unramified and universally injective but need not be
  universally closed; the hypothesis `hg` excludes this counterexample.
- Nonreduced closed immersions remain allowed. No reducedness, Noetherian, separated,
  quasi-compact, characteristic or finite-presentation assumption is introduced.

Searches for an existing statement (all `msearch.py` calls used group Q03 and this item):

- LeanFinder: `A universally closed morphism of algebraic spaces is a closed immersion iff
  unramified and universally injective`. Eight results, all scheme universal-closedness
  declarations, including `instUniversallyClosedOfIsClosedImmersion` and
  `universallyClosed_iff`; no algebraic-space criterion.
- Loogle: `"IsClosedImmersion", "IsUnramified"`. Zero results.
- Mathlib grep: `AlgebraicSpace|IsClosedImmersion.*[Uu]nramified|[Cc]losedImmersion_iff`
  in `AlgebraicGeometry`. Four results in scheme `Morphisms/ClosedImmersion.lean`;
  no algebraic-space statement.
- LeanSearch: `A universally closed morphism of algebraic spaces is a closed immersion
  if and only if unramified and universally injective`. Eight scheme declarations,
  including `UniversallyClosed` and `isClosedImmersion_iff_isAffineHom`; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `MapIsUniversallyInjective`,
  `MapIsClosedImmersion`, closed-immersion iff names and this exact node id: no matching
  theorem. Existing Sheaf closed-immersion statements use the same
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` expression.
- A further search for universal injectivity and unramifiedness found only scheme open-locus
  results `UniversalUnramifiedRadicialOpen` and `UniversalClosedImmersionOpen`, not this
  algebraic-space criterion. The chosen full theorem name was absent from Mathlib,
  the upstream declarations index and both project source roots.

No statement correction and no STATEMENT-DISPUTED issue. Initial compilation through
`scompile.py` passed both sandbox and library checks without errors or additional warnings.

## Validation

The delivery dry run and final push are performed with `deliver2.py` after the single-file
server compile. The exact theorem signature is stored verbatim in the node's `lean.statement`.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
