## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit` states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_finitePresentation_limit_of_integral`,
with one postponed proof (`sorry`) and no new definitions. It formalizes the full
statement of lem-sfb-integral-space-finite-presentation-limit, including affine
transitions, qcqs stages and the universal property in algebraic spaces over X.

The inherited unchanged-item rejection concerned the accepted Q151 stage-1 delivery.
The current item has no Lean record or reviewed_lean field, so the stage-2 handoff in
brief-stage2 section 0 applies. No repair note for this item is present. This delivery
preserves the accepted statement and proof split.

Sources read: Stacks `spaces-limits.tex`, Tag 09YA,
`lemma-integral-limit-finite-and-finite-presentation`, statement and relative-Spec proof;
`spaces-properties.tex`, `definition-separated` and
`lemma-characterize-quasi-separated` (Tag 0AHR), statement and proof. The latter tests
absolute quasi-separatedness using arbitrary pairs of affine schemes over the space.
This avoids imposing relative qcqs on S or silently identifying the relative and
absolute diagonals.

Hypothesis and clause correspondence:

- A scheme S and algebraic spaces Y, X over S: `{S : Scheme.{u}}`
  and `{Y X : AlgebraicSpace S}`. These are the actual fppf-sheaf full subcategory
  from def-trf-algebraic-space, with its natural-transformation morphisms.
- The morphism p: `p : Y ⟶ X`.
- Integrality: `hp : IsRepresentableWith (fun _ _ f ↦ IsIntegralHom f.left) p.hom.hom`.
  This uses the recorded scheme notion, requiring representing integral scheme maps
  after each scheme base change; no integrality of the source space is assumed.
- Quasi-compact X: `hqc : CompactSpace (Point X.obj.obj)`, using the recorded point
  classes and final atlas topology. CompactSpace has no Hausdorff hypothesis.
- Absolute quasi-separated X: `hqs` quantifies over all affine `U V : Over S`
  mapping to X and requires `CompactSpace (Point (Limits.pullback a b))`.
  This is exactly the equivalent test in Tag 0AHR, including for non-qcqs S.
  The presheaf pullback is represented by a scheme because X has representable
  diagonal. It is the absolute test, not just the relative diagonal over S.
- Small nonempty directed set: existential `I : Type u`, `PartialOrder I`,
  `Nonempty I`, and `IsDirected I (· ≤ ·)`. The index lives in the same universe
  as scheme data, as required by the project's limit convention.
- Spaces Y_i over X and compatible X-transition maps: `D : Iᵒᵖ ⥤ Over X`.
  The stage is `(D.obj i).left`, its structure map is `(D.obj i).hom`, and the
  transition is `(D.map f).left`. Functoriality includes identity/composition laws;
  the Over morphism condition is the equation that the transitions are over X.
  Opposite order reverses j ≥ i to Y_j → Y_i.
- Projections Y → Y_i over X, compatible with every transition:
  `π : (Functor.const Iᵒᵖ).obj (Over.mk p) ⟶ D`. Each component has the required
  domain, codomain and triangle over X, and naturality is compatibility.
- Finite structure maps: the first stage conjunct is
  `IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) (D.obj i).hom.hom.hom`.
- Finite presentation: the next three stage conjuncts are `MapIsQuasiCompact`
  of the structure map, `MapIsQuasiCompact` of its relative diagonal, and
  `MapIsLocallyOfFinitePresentation (D.obj i).hom`. These are precisely
  quasi-compact, quasi-separated and locally finitely presented on etale charts.
- Quasi-compact stages: `CompactSpace (Point (D.obj i).left.obj.obj)`.
- Absolutely quasi-separated stages: the same affine-pair compactness condition as
  hqs, with target `(D.obj i).left`. This is separate from relative finite presentation.
- Affine transitions: for all i, j and f, `IsRepresentableWith`
  of `IsAffineHom` applied to `(D.map f).left.hom.hom`.
- Limit with the specified projections: `Nonempty (IsLimit (Cone.mk (Over.mk p) π))`.
  IsLimit lifts every cone and characterizes the lift uniquely. Its ambient category
  is Over X in algebraic spaces, so the test vertex can be every W/X, with no
  affineness or representability hypothesis. It is the asserted Hom bijection.

Dependency declarations used, with their modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `AlgebraicSpace.Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  its imported `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocallyOfFinitePresentation` (the recorded chart test).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact`.
- `Mathlib.CategoryTheory.Limits.IsLimit`: `CategoryTheory.Limits.IsLimit`;
  `Mathlib.CategoryTheory.Comma.Over.Basic`: `CategoryTheory.Over`.

The already-landed definition nodes def-sfb-space-morphism-properties and
 def-sfb-proper-curve-moduli are added to stmt_deps to record the two reused
interfaces; no private copies or new helper notions are introduced. The size convention
is metatheoretic and is implemented by explicit `universe u` and explicit binders.

Proof imports: the stated proof nodes lem-a1-space-etale-open-image and
lem-trf-space-fibre-products-etale-covers are imported without public visibility.
The scheme Mathlib matches for def-weil-finite-integral-morphism,
lem-weil-pbc-affine-morphism-permanence, and
lem-weil-pbc-affine-source-separated-target-affine-morphism are covered by Finite,
Separated and Limits. The other proof nodes have no recorded Lean declaration yet:
lem-sfb-space-relative-spec-correspondence, lem-sfb-space-integral-algebra-fp-colimit,
lem-sfb-space-affine-locality, lem-sfb-qc-space-affine-etale-atlas,
lem-sfb-space-affine-limits-schematic-stages. They are proof prerequisites only and
are named in the full natural-language proof docstring; no missing statement notion
or data construction is hidden by them.

Edge cases checked: empty X (and hence empty Y), empty S, identity integral morphisms,
non-Noetherian bases, integral algebras not finite or finitely presented, finite stages
with noninjective algebra colimit maps, nonschematic X, and non-quasi-separated S.
A singleton directed set covers the empty or identity finite-presentation examples.
No nonempty point or affine-source hypothesis was added; only the index is nonempty.
Absolute quasi-separatedness uses all affine pairs, even with distinct maps to S.
The universal property tests all algebraic spaces W/X, including Y itself and the
empty space. There is no stronger surjectivity or closed-immersion transition clause.
No statement dispute or statement correction is needed.

Searches performed:

- msearch.py leanfinder: "An integral morphism of algebraic spaces over a quasi compact
  quasi separated base is a directed inverse limit of finite finitely presented
  morphisms". Eight results, including scheme integrality, finiteness and normalization
  results, but no algebraic-space approximation statement.
- msearch.py loogle: `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.IsFinite`.
  Three hits: IsFinite.instIsIntegralHom, IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
  IsFinite.eq_inf, all about scheme morphisms, not this statement.
- msearch.py grep: `integral.*limit.*finite|AlgebraicSpace`, AlgebraicGeometry.
  Zero Mathlib hits.
- rg of WeilConjectures and Sheaf for integral/space/limit/finite-presentation names
  and the exact item id: no existing statement for algebraic spaces. Read the scheme
  analogue `Scheme.Hom.exists_finiteApproximation_of_isIntegralHom` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation`
  (Tag 09YZ, line 341): its X and S are schemes, so it cannot attach this node.
- rg for MapIsQuasiCompact, MapIsLocallyOfFinitePresentation and chartwise morphism
  properties located the existing interfaces above; their full signatures and
  docstrings were read and reused. No second definition is written.

Validation: scompile.py compiled this module separately both in its sandbox namespace
and as `Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit`, taking about
1.9 and 1.8 seconds, with no errors or unexpected warnings. Explicit autoImplicit=false
checks all term and universe binders. No theorem is proved and no definition has sorry
data. The node's lean.statement is the verbatim theorem signature from the module.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
