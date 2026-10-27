## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedComparisonAffineChartSystems.lean`
states `AlgebraicGeometry.exists_closedComparison_affine_chart_systems`.  It uses a
functor `X : Iᵒᵖ ⥤ Scheme` and a natural transformation `f : X ⟶ S`; `Over (op i₀)`
is the upper tail.  The theorem has no definition data and its proof is exactly `sorry`.

The hypotheses are rendered as follows.  `I` is an explicitly bound universe-`u`
`PartialOrder` with `[Nonempty I]` and `[IsDirected I (· ≤ ·)]`; `X` and `S` are
inverse diagrams of `Scheme.{u}`; every target is `CompactSpace` and
`QuasiSeparatedSpace`; every base transition is `[IsAffineHom (S.map t)]`; each
`f.app i` has `[LocallyOfFiniteType]` and `[QuasiCompact]`; and `hclosed` gives
`IsClosedImmersion` for the canonical pullback comparison.  The two cones, their
`IsLimit` witnesses, and `i₀` are explicit binders.

The conclusion is one existential tuple `A B b V₀ W₀`.  `Finite A`, `Finite B`,
the two initial covering equalities, and the affine-open predicates render the finite
affine covers.  `W₀ a ≤ f.app (op i₀) ⁻¹ᵁ V₀ (b a)` renders the required image
containment.  The two `⨆` equalities over every `i : Over (op i₀)` render the stage
covers; the corresponding two equalities using `cS.π.app` and `cX.π.app` render the
limit covers.  The next two clauses state that every pulled-back chart is affine.
The two `Nonempty (IsLimit ...)` clauses state that restriction of both original
cones to the upper tail remains limiting; the following two families state that each
pulled-back chart cone is limiting.

For every `a`, witnesses `r` and `rLim` are supplied.  The first displayed equation
says that `r.app i` is the restricted morphism and commutes with the original charts;
the second says that `rLim` is the restriction of the limit morphism.  The
`FiniteType` clause on `(r.app i).appTop` renders the finite-type coordinate maps.
For every `j ⟶ i`, the `IsClosedImmersion` clause renders the restricted comparison.
The witness `q` is the map out of the categorical ring pushout; its two equations
identify both pushout inclusions with the two coordinate maps, and
`Function.Surjective q.hom` renders surjectivity of the tensor/pushout coordinate
map.  The final witnesses `eV`, `eW`, and `g` state the canonical spectrum
identifications for the colimits of the global-section diagrams, compatibility of
both isomorphisms with all projections, the colimit compatibility equation for `g`,
and `eW.hom ≫ Spec.map g = rLim ≫ eV.hom`.

Dependency declarations used (all are existing Mathlib records or definitions):

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `QuasiCompact` is from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (used by `opensDiagramι`).
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `Cone`,
  `IsLimit`, `Over`, and `CategoryTheory.IsFiltered` infrastructure.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `opensDiagram`, `opensCone`, `opensDiagramι`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.Algebra.Category.Ring.Constructions` (via the imported tensor map
  modules): categorical pushout and its tensor-product implementation.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `QuasiSeparatedSpace`.

Edge cases checked: `I` is required nonempty exactly as the source's directed set;
`A` and `B` are permitted to be empty, so empty schemes and empty covers are not
excluded; later pulled-back charts may be empty (including the zero-ring affine
case); no separatedness or quasi-separatedness of `X` was added; nonreduced closed
immersions are allowed; `i₀` is arbitrary; and the theorem does not require the
original squares to be cartesian.  The upper-tail limits are represented by the
actual `opensCone` objects, so no additional universe restriction is introduced.

Searches for an existing declaration:

- `msearch.py ... leanfinder "compatible finite affine charts for inverse systems ..."`:
  eight hits, led by `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`; no
  declaration constructs these simultaneous covers, closed comparisons, and ring
  colimit data (no match).
- `msearch.py ... loogle '"IsClosedImmersion", "IsAffine"'`: five Mathlib hits,
  including `IsClosedImmersion.instIsAffineHom` and affine closed-immersion criteria;
  none states this theorem (no match).
- `msearch.py ... leansearch "finite compatible affine open covers ..."`: eight hits,
  including `isLimitOpensCone`, `Scheme.directedAffineCover`, and affine-cover
  constructors; these are components only (no match).
- `msearch.py ... leansearch "Open inverse image chart limits ... colimit rings"`:
  eight hits including `isLimitOpensCone` and `Spec.map`; no complete theorem.
- `msearch.py ... grep 'opensDiagram|isLimitOpensCone|pullbackSpecIso' AlgebraicGeometry`:
  25 Mathlib hits, all component APIs (`isLimitOpensCone`, `pullbackSpecIso`, etc.);
  no existing combined statement.
- `rg` over `lean/Sheaf`, `lean/WeilConjectures`, and the upstream name map found no
  declaration or duplicate of this item.

The source was read at `literature/stacks-project/limits.tex`, Tag 05M5 (with the
auxiliary chart construction from Tags 01YX and 01YW); the blueprint unit and its
ancestor were also read.  The file compiles cleanly with `scompile.py`; the only
proof placeholder is the expected theorem `sorry`.

## Second reading by Q04

I reread the node and the generated signature clause by clause.  The directed index,
all base and morphism hypotheses, the closed-comparison hypothesis, both limiting
cones, and the chosen initial index are present.  The existential data has finite
index types, the map `b`, both initial affine covers, stage and limit cover equalities,
affineness of every pulled-back chart, tail-limit witnesses, restricted morphisms,
finite-type coordinate maps, closed comparisons, surjective pushout maps, and the
colimit-spectrum isomorphisms with projection and morphism compatibility.  The
`opensDiagram`/`opensCone` objects are exactly Mathlib's canonical inverse-image
charts, and categorical pushout is the canonical tensor-product object.  No mismatch
or omitted hypothesis was found; no change was needed in this second reading.
