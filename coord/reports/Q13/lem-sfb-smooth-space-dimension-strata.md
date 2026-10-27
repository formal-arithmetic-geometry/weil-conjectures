## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSpaceDimensionStrata` states
`AlgebraicGeometry.AlgebraicSpace.exists_smooth_dimension_strata` with one `sorry`.
It introduces no definitions, auxiliary theorem obligations, new nodes, or dependency
modules. The mathematical statement is unchanged. The only additional statement
dependency is the already landed `def-sfb-proper-curve-moduli`, whose general interfaces
supply the existing point map and scheme-target morphism properties. No proper-curve
hypothesis is used.

Sources read: Stacks `morphisms.tex`, lemma-smooth-omega-finite-locally-free (02G1),
definition-smooth-relative-dimension (02G2) and the following paragraph;
`spaces-more-morphisms.tex`, lemma-smooth-omega-finite-locally-free (0CK5);
`spaces-morphisms.tex`, lemma-dimension-fibre-after-base-change (04NS), especially (1);
`decent-spaces.tex`, lemma-dimension-decent-space (0A4J). These give exactly the smooth
chart dimension, base-change formula, and topological dimension comparison in the node.
The seven proof steps of the accepted split are included in the theorem docstring.

Hypothesis and conclusion correspondence:

- A scheme B and an algebraic space mapping to it: `S : Scheme.{u}`, `X : AlgebraicSpace S`,
  `T : Over S`, `f : X.obj.obj ⟶ yoneda.obj T`. Here B is `T.left`. The ambient S merely
  expresses the existing relative algebraic-space API: the structural case is S=B,
  T=`Over.mk (𝟙 B)`, and the canonical structure map of the presheaf. Conversely any map
  X→h_T describes the same algebraic space over T. All scheme changes over B are included:
  h:B'→B is represented by T' with structure h≫T.hom and its arrow to T.
- Smooth on every representable étale scheme chart: `hsmooth : MapToSchemeIsLocally
  (@Smooth) X T f`. Expanding the recorded definition gives precisely every U,a with
  `IsEtale a`, and smoothness of `(yoneda.preimage (a ≫ f)).left`.
- Atlas topology and open subspaces: `Point X.obj.obj`, the existing
  `pointTopologicalSpace`, and `A : ℕ → OpenSubspace X`. No point model or topology is copied.
- Finite nonnegative chart-independent dimension: `ν : Point X.obj.obj → ℕ`, together
  with the first universal clause, identifies every chart value with ν at its image.
  There is no affine restriction on U. Thus every pair of charts gives the same finite
  natural number. `schemePointMap a v` is the canonical residue-field point class.
- U_b and the distinguished point: `(yoneda.preimage (a ≫ f)).left.asFiber v` uses
  Mathlib's actual scheme pullback along `T.left.fromSpecResidueField (g v)` and the
  canonical lift v. Mathlib's `fiberHomeo` identifies its points with the inverse image
  of {g(v)}, so this is the unique lift specified in the node. No arbitrary field lift
  or local-ring dimension is substituted.
- Dimension at a point: `topologicalKrullDimAt` is the recorded infimum of the
  `topologicalKrullDim` of open neighbourhoods. The cast `(ν (...) : WithBot ℕ∞)` gives
  its finite integer value, excluding both bottom and infinity.
- Local constancy: `IsLocallyConstant ν` on the already specified atlas topology.
- Clopen strata: for each n, `IsClopen {x | ν x = n}` and
  `pointImage (A n).val.ι = {x | ν x = n}`. `A n` is an actual open subfunctor,
  represented by open immersions on every scheme test, not merely a subset of points.
- Partition: `∀ x, ∃! n, x ∈ pointImage (A n).val.ι` includes coverage and disjointness.
- Every scheme base change: `∀ (T' : Over S) (h : T' ⟶ T)`. The new space is the actual
  presheaf `Limits.pullback f (yoneda.map h)`, f' is `pullback.snd`, and q is `pullback.fst`.
  For every representable étale chart a of this pullback the statement asserts
  `Smooth ((yoneda.preimage (a ≫ pullback.snd ...)).left)`.
- Pointwise base-change dimension equality: the dimension function on the pullback is
  written as the explicit function `ν ∘ mapPoint (pullback.fst ...)`. Its equality with
  `topologicalKrullDimAt` for EVERY chart lift specifies ν_f' itself, by the same
  characterization as ν_f. Hence the formula ν_f'(x')=ν_f(q(x')) is part of the statement,
  not an extra assumed compatibility. Its local constancy is explicitly included.
- Equality of strata as subspaces: `((A n).val.preimage (pullback.fst ...))` is the literal
  subfunctor pullback, not a point-set replacement. Its inclusion is representable by
  open immersions; its point image is clopen and exactly the new dimension-n locus.
  Thus the fibre product X_n×_B B' IS the dimension stratum on the pulled-back space.
  The canonical fibre product is supplied by the existing limits API; closure of
  sheaf fibre products as algebraic spaces is the imported fibre-products node.
- The extra hypotheses are confined to the last implication: `MapToSchemeIsSeparated
  X T f`, `MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`,
  `MapIsQuasiCompact f`, and `MapIsQuasiCompact (pullback.diagonal f)`. These are exactly
  closed-immersion scheme tests of the diagonal, local finite presentation on charts,
  quasi-compact affine tests, and quasi-compactness of the diagonal. Their definitions
  were read in ProperCurveModuli. No global compactness of B is assumed.
- Every geometric fibre: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (g : Spec (.of Ω) ⟶ T.left) (n : ℕ)`. It includes ALL maps from algebraically closed
  fields in the site universe, not just residue-field closures. The fibre is the actual
  presheaf pullback of `(A n).val.ι ≫ f` along `yoneda.map (Over.homMk g rfl)`.
- Pure topological dimension: `∀ C ∈ irreducibleComponents (Point (...)),
  topologicalKrullDim C = (n : WithBot ℕ∞)`. C carries its subspace topology, and the
  irreducible components are the maximal nonempty irreducible closed subsets. Empty
  fibres have no components; the universal form expresses exactly the node's
  nonempty-fibre purity assertion and adds no nonemptiness requirement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsAlgebraicSpace`. The fppf sheaf condition and the actual diagonal/atlas
  are part of this recorded definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`;
  smoothness in the signature is `Smooth`, with no deprecated IsSmooth alias.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`, using `Point` and `schemePointMap` from AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`. The actual `Scheme.Hom.fiber` and `.asFiber` from
  `Mathlib.AlgebraicGeometry.Fiber` use this residue-field spectrum.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`. No algebraic extension condition is imposed on Ω.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally`,
  `MapToSchemeIsSeparated`, `MapIsQuasiCompact`, `mapPoint`. The landed node carrying
  these notions is added to stmt_deps, as permitted by brief-stage2 §5.
- Proof imports cover all recorded proof dependencies with usable landed modules.
  The nodes `lem-sfb-space-component-generic-chart-dimension` and
  `lem-sfb-etale-topological-dimension-at-point` have no Lean records yet in the read
  clone, so they have no module to import; they remain explicitly cited in the proof
  docstring. Neither introduces any object needed to type this statement. The already
  stated lem-sfb-space-local-fibre-dimension-open is imported solely as a proof input;
  the signature does not duplicate or redefine its `localFibreDimension` function.

Edge cases checked before writing: the empty space admits the empty function ν and all
empty strata; no Nonempty hypothesis appears. Absent dimension indices have empty
strata. Dimension zero is included because the codomain and indices are ℕ. Mixed
smooth dimensions on different connected components are allowed. Empty B' and empty
geometric fibres are included. No characteristic restriction, Noetherian, affine,
separated, finite-presentation or finite-type assumption is imposed on the main
chart/base-change assertions. The last two geometric hypotheses are only used by the
purity implication. The same universe u is used for test fields and schemes, matching
the recorded big-site convention and allowing their residue fields and algebraic
closures. No independent smaller test universe, arbitrary selected chart, hollow
hypothesis, file-local notation, or hidden let binder is used.

Searches actually run through `msearch.py Q13 lem-sfb-smooth-space-dimension-strata`:

- LeanFinder: "Smooth algebraic spaces have locally constant local fibre dimension and
  clopen dimension strata compatible with arbitrary base change". Eight scheme smoothness
  and relative-dimension hits; no algebraic-space theorem.
- Loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.SmoothOfRelativeDimension".
  One result, `SmoothOfRelativeDimension.smooth`; it does not give the statement.
- LeanSearch: "Smooth algebraic spaces have locally constant fibre dimension strata".
  Eight scheme smoothness/relative-dimension hits; no algebraic-space result.
- Mathlib grep: `localFibreDimension|smooth.*[sS]trat|[dD]imension.*[sS]trat` in
  AlgebraicGeometry. Zero hits.
- `rg` with that pattern in lean/WeilConjectures and lean/Sheaf found scheme flat
  stratification results and the algebraic-space localFibreDimension definition and
  bounded-open theorem. These do not assert the smooth clopen strata/base-change/purity
  conjunction. Exact node-id grep in lean/WeilConjectures had no hit.
- Source grep for the proposed declaration name and upstream names was also checked.
  No declaration with the same name or complete statement was found.

Validation: `scompile.py Q13 lem-sfb-smooth-space-dimension-strata` compiled both its
private sandbox module and its library module cleanly, each in under two seconds after
slot acquisition. The first attempt exposed unqualified `pullback` resolving to the
algebraic-space étale pullback functor; all object-level occurrences are now qualified
as `Limits.pullback`. No unresolved statement dispute or node fault remains.

## Second reading by Q13

The dispatcher explicitly prohibits starting other agents; this is an honest second
pass by the same worker, with the node and final Lean module open. Independent review
is left to the maintainer's delivery review, as the brief specifies.

I rechecked the chart quantifier: it ranges over all étale scheme charts, without
IsAffine or surjectivity assumptions. The dimension uses the fibre's topological
neighbourhood dimension, not the stalk dimension. I checked that each base-change
chart maps to the second projection, while the dimension comparison uses the first
projection. The stratum is its literal subfunctor preimage and has the correct point
image and openness predicate; no arbitrary comparison isomorphism is assumed. I
expanded the four final morphism-property premises and matched each with the node.
The purity expression quantifies over every algebraically closed field and every
map of its spectrum, and applies Krull dimension to each component as a subspace.
The distinction between existence of ν and construction of data is harmless here:
this is the node's theorem assertion, with its proof postponed; no definition makes
an arbitrary choice from the theorem. The only change from the first pass was the
pullback-name qualification required by compilation. No mathematical change was
needed.
