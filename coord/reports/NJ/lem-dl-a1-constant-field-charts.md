## Worker report

The module `Sheaf.Paper.DlConstantFieldCharts` states
`WeilConjectures.dlConstantFieldCharts`, with its proof postponed. All other explicit
declarations are clause packages or real constructions belonging to this node.
There are no postponed definitions, extra axioms, or proofs of new theorems.

The statement is expressed in the published `Scheme.MiddleExtensionCurve` interface.
Its `C` is W_0, `U` is U_0 and `j` is the given dense open immersion. The input X_0
is unnecessary to the conclusion: smooth relative dimension one restricts to W_0,
and conversely every W_0 quantified here is admitted by the original statement by
taking X_0=W_0. This changes no hypothesis or case. The bundled smoothness, pure
dimension, separatedness and finite type in `MiddleExtensionCurve` follow from the
stated smooth affine finite-type W_0 and its open U_0. The theorem additionally retains
`[IsAffine c.C.left]` and `[SmoothOfRelativeDimension 1 c.C.hom]`.

Clause matching:

- The finite-field datum is `D : FiniteFieldDatum`; `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`,
  and the algebraic closure `Ω` are explicit. The weight clause quantifies over the
  stipulated `iota : Ω ≃+* ℂ`. No choice of coefficient stage or integral Weil lattice
  is imposed on the input sheaf.
- Finite type and the dense open are the `finiteU`, `finiteC`, `quasiCompactU`,
  `quasiCompactC`, `openImmersion`, and `dense` fields of the recorded curve interface.
  The first conjunct says the boundary `(Set.range c.j.left)ᶜ` is finite, and the next
  says every one of its points belongs to `closedPoints c.C.left`.
- The chosen boundary point is the subtype `s`, with `s.val ∉ Set.range c.j.left`.
  The embedding is the actual residue-field homomorphism `ι`, with its base-field
  compatibility written explicitly using `residueFieldAlgebraMap`.
- `DlPointedConstantChart` retains the residue field by `residue`, a ring equivalence
  with `D.extensionSubfield m positive`, and `embedding`, saying its composite with
  the subfield inclusion is exactly the chosen embedding. Thus this is the same
  finite field, not an arbitrary extension of larger degree. Its finiteness and
  finite degree over k_0 follow from that equivalence and the finite subfield.
  Transporting the curve along this equivalence gives literally the curve over
  κ(s). This is a presentation of the same objects, not a statement correction.
- The new finite-field datum is the existing `constantExtensionDatum`; `curve.C`
  is V_0 over that field. `chart` is its open immersion into the existing
  `constantExtensionModel` W_0 × k'_0. `affine`, `dimension`, and `connected` state
  affineness, smooth relative dimension one and geometric connectedness; finite
  type comes from the same recorded curve interface.
- `t` is a closed point; `rational` says the structural field map k'_0 → κ(t) is
  bijective, exactly rationality over k'_0. `image` says h(t)=s. `residueMap` says
  the induced map κ(h(t)) → κ(t) is bijective, using the actual induced residue map;
  `image` identifies its source with κ(s). `etale` is Etale of the actual projection
  composed with the chart open immersion.
- `curve.j`, `openChartU`, and `cartesian` retain j_V, h_U, and the actual Cartesian
  square U_V=U_0 ×_W V_0. `curve.dense` gives density; `openConnected` gives geometric
  connectedness of U_V; `finiteBoundary` and `closedBoundary` give its finite closed
  boundary. `square` records the arithmetic open-chart square.
- `geometricMap` and `geometricOpenMap` are real compositions of geometric base-change
  maps and the published associativity isomorphisms. The return equations in
  `DlPointedChartAdicData` say h g_V = g_W^m h, on both V and U_V.
- `DlChartRestriction.pull` acts on the actual common-stage Weil heart. Its natural
  `carrier` comparison fixes the underlying functor on objects and arrows to the
  recorded `commonStageDerivedPullback`. Its `weil` equation fixes its Weil datum
  to the pullback of `localQbarWeilIterate`, including the actual normalized
  pullback-composition isomorphisms in `dlChartReturnComparison`. Thus the existential
  restriction is characterized, rather than being an arbitrary substitute map.
- `DlChartOpenComparison.lisse` gives lissity of G_V. `higher` gives the comparisons
  for exactly `r = 0 ∨ r = 1`, and `natural` is their morphism naturality. The
  cohomology comparison uses `ConstructiblePullbackComparison`, whose truncation
  unit/counit and cohomology formula normalize it. The `shift` equation additionally
  fixes its shift structure to the published `fieldCommonPullShift`, whose signed
  Roos and finite-stage normalization excludes arbitrary shift signs. `normalization` identifies the
  higher comparison with cohomology of `dlChartDerivedExchange`, the explicitly
  defined counit mate of the normalized inverse-image square.
- `ordinary` and `degreeZero` identify the degree-zero comparison with ordinary
  `qbarCurveWeilOrdinaryPushforward`. `boundary` is exactly the δ square for the
  published `DlOpenLisseSES` and `DlOpenImageData.boundary`. It allows every
  isomorphic presentation of the pulled-back short exact sequence. The latter
  boundary is already fixed by its distinguished heart-triangle formula.
- `localImage` uses `DlChartLocalConjugacy` for both higher images at s and t with
  exponent 1. It uses the published `localQbarClosedStalk` and
  `localQbarClosedFrobeniusStalk`, quantifies over all allowed geometric-point
  embeddings, and states the isomorphism intertwines F_t and F_s. `equalSize`
  gives q_t=q_s.
- `localOpen` quantifies over every closed v of U_V and retains its closed image u.
  It states q_v=q_u^e and the conjugacy F_v=F_u^e. The exponent is the existing
  `Scheme.Hom.residueDegree` of the actual h_U at v, with its actual residue-field
  map; no independent degree is supplied. `pure` is the unchanged
  `SfIsPunctuallyPureOfWeight` predicate at the same real weight on both sides.
- The second theorem conjunct supplies, for every family `I`, the same normalized
  two-degree comparison package with D=E and m=1,
  for finite-type open neighborhoods, including its δ square. Its restrictions
  are fixed to the actual inverse image by the carrier and Weil equations. The last conjunct,
  `DlOpenImageSuccessive`, writes the equality for two successive restrictions
  versus direct restriction on the actual derived counit mates, with both
  canonical pullback compositors inserted, then applies cohomology in degrees
  zero and one. Their normalized higher/degree-zero formulas identify these with
  the requested comparisons; hence the equality also respects the boundary maps
  and induced local operators.

Dependency declarations used:

- `WeilConjectures.DeligneLaumon.AffineLine.Defs`: the recorded conventions module.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Hom.residueFieldMap`, `Hom.residueFieldAlgebraMap`, `Hom.residueDegree`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and its field-extension convention.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: fibre products;
  the statement keeps `IsPullback` so any chosen realization of U_V is included.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: the recorded adic lisse systems;
  the actual carrier lissity predicate is `DlOpenIsLisse`/`IsCommonStageLisse`,
  already used by the recorded open-image-delta dependency.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible`.
- `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`: the recorded ordinary image.
- `Sheaf.Paper.SfCommonStageDirectImage`: `sfModelDerivedPush`,
  `sfModelDerivedAdjunction`, `sfModelPullComposition`, `sfModelDerivedExchange`.
- `Sheaf.Paper.WeilOpenImageDelta`: `DlOpenLisseSES`, `DlOpenImageData`,
  `DlOpenImageRestriction`, `DlOpenIsLisse`, `dlOpenHigherImage`,
  `dlHigherGeometricComparison`, `dlOpenOrdinaryAdjunction`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`,
  `localQbarPullbackComposition`, `localQbarWeilIterate`, `localQbarClosedStalk`,
  `localQbarClosedFrobeniusStalk`.
- `Sheaf.Paper.AdicPunctualWeights`: `SfIsPunctuallyPureOfWeight`.
- `Sheaf.Paper.GeometricHypotheses`: reuses Mathlib `GeometricallyConnected`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`.
- `def-dl-a1-constant-extension-data` owns the existing definitions in
  `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: `constantExtensionDatum`,
  `constantExtensionModel`, `constantExtensionOriginalModel`,
  `constantExtensionProjection`, `constantExtensionSheet`,
  `constantExtensionFiberIso`, and `constantExtensionHeartForget`.
  The chart cites this definition node rather than the theorem node. No theorem
  choice supplies these definitions, and none is copied or modified.
- All recorded modules of stated proof dependencies are imported, privately when
  used only by the proof plan. Mathlib matches are imported from their recorded
  files. The theorem docstring gives all thirteen proof steps and names their inputs.

Edge cases checked before writing: empty W has no boundary point; j=id has empty
boundary; disconnected smooth W selects the component through the rational lift
without assuming W geometrically connected; a nontrivial field of constants is
allowed (e.g. A^1/F_4 viewed over F_2). Residue degree m=1 and m>1 are both included;
positive m is retained before using m-1 in the published positive-power convention.
A degree-two closed point of A^1/F_2 tests the rational lift and F_t=F_s rather than
an unintended square. Zero sheaves and rank-zero fibres have vacuous purity and
valid zero-dimensional fibre comparisons. No semisimplicity or purity is used for
the comparison. Ordinary restrictions allow identity and empty open maps. The
coefficient universe is the universe of the finite-field coefficient datum used by
the published local Qbar fibre API; no site object/morphism universe is identified.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: “Smooth curve finite field geometrically connected
  affine chart at a closed point with etale restriction of higher direct images
  and local Frobenius”. Eight hits, including smooth relative-dimension charts,
  standard-smooth etale presentations and Scheme.Etale; none supplies this statement.
- `msearch.py`, Loogle: `"GeometricallyConnected"`. Twelve hits, including
  `AlgebraicGeometry.GeometricallyConnected` and base-change instances. These give
  the existing definition, not pointed charts with adic/Weil comparisons.
- `msearch.py`, grep: `constantFieldChart|constant_field_chart|open_image_comparison`
  in Mathlib/AlgebraicGeometry. Zero hits.
- `msearch.py`, LeanSearch: “Etale restriction of l-adic higher open direct images
  with local Frobenius and constant field charts”. Eight hits concern restrictions
  of schemes or ordinary scheme modules; none is the requested adic statement.
- `rg` of the source project's WeilConjectures, the side project's lean/Sheaf and
  `dag/lean_names_upstream.json` for the item id and constant-field-chart names found
  no declaration. A conceptual search for constant extensions located the landed
  `ConstantExtensionWeilHeartEquivalence` module, which is reused. Its statement
  contains no pointed affine chart or higher-open-image/connecting-map comparison,
  so it is not an existing match for this item.
- Mathlib residue-field source inspection found `Scheme.Hom.residueDegree`; an
  initial draft helper for that number was removed in favor of this existing notion.

The already landed `def-zl-field-weil-shriek-shift-data` is also added to
`stmt_deps`, reusing `WeilConjectures.fieldCommonPullShift` from
`Sheaf.Paper.FieldWeilShriekShiftData` to normalize the shift structure.
The added definition dependencies have no path back to this item.
No mathematical statement correction is needed.
No mathematical defect was found. Source inspection included the actual
K-injective formula in Stacks 0D6G, the rational-point criterion in 04KV, and the
current main-20261015 missing-point paragraph.

## New nodes

`def-dl-a1-constant-extension-data` is an `existing: true` ownership record for
seven definitions already landed in
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`. It introduces no Lean file.
This repairs F1 of the return on immutable head `e8fc754697dc`.

Its hypotheses are `D : FiniteFieldDatum.{u}`, `m : ℕ`, `hm : 1 ≤ m`,
`X₀ : Over (Spec (.of D.k₀))` with finite type expressed by
`[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`, and, for the forgetful
functor, `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, and an algebraic closure `Ω`
of `ℚ_[l]`. These are the ambient binders in the existing module. The separatedness
binder there is used only by its main theorem and is not included in these definitions.

Clause matching for the new node:

- `constantExtensionDatum` keeps `p` and `k`, sets `a := D.a * m`, `q := D.q ^ m`,
  and `k₀ := D.extensionSubfield m hm` with the existing subfield inclusion.
- `constantExtensionModel` is literally `Over.pullback` along the spectrum of
  `D.extensionEmbedding m hm`. It retains the second structural projection.
- `constantExtensionOriginalModel` composes that structural map with the same
  spectrum map to the original base. `constantExtensionProjection` is the first
  pullback projection, bundled over the original base.
- `constantExtensionSheet` is the specified `pullback.lift`, using the subfield
  inclusion into `D.k`. Its two projections fix it uniquely.
- `constantExtensionFiberIso` is `asIso` of that sheet map followed by
  `zlFiberMap D (constantExtensionProjection ...)`; the named isomorphism theorem
  supplies only the proof, while the forward morphism is the actual construction.
- `constantExtensionHeartForget` is the full-subcategory inclusion composed with
  `sfCommonStageWeilForget`; hence it forgets heart membership and the Weil map on
  both objects and morphisms.

The new node reuses the recorded `FiniteFieldDatum` and `extensionSubfield`/
`extensionEmbedding`/`geometricFiber` from `Sheaf.Paper.FiniteFieldFiber`, the
Mathlib pullback and finite-type notions, the actual Weil pairs and forgetful
functor from `Sheaf.Paper.SfWeilSheafComplex`, and the common-stage heart property
from `Sheaf.Paper.SfConstructibleHeart`. Their source signatures and docstrings,
and the live constant-extension source returned by `scompile.py --source`, were read.
The cases `m=1`, nontrivial `m`, and the empty scheme retain their usual pullbacks;
there is no component or rational-point choice in this definition node. The
forgetful functor includes the zero object and every constructible Weil sheaf,
without lissity or semisimplicity. Scheme and coefficient universes remain those
of the landed definitions, with independent `u` and `v` for this forgetful functor.

New-node searches (full wrapper records are in `mathlib_searches`):

- LeanSearch, “Finite constant field extension of a finite field scheme and canonical
  geometric fiber base change isomorphism”: eight hits, including
  `FiniteField.Extension`, finite base-change stability, and scheme fibre maps;
  none is this finite-field datum/base-change/heart-forgetful package.
- Loogle, `"constantExtensionDatum"`: zero hits.
- Mathlib grep, `constantExtensionDatum|constantExtensionModel|constantExtensionHeartForget`:
  zero hits. The same source grep in `WeilConjectures` gave no hits.
- DAG and `lean/Sheaf` grep found the existing definitions in the theorem module
  and its theorem-node declaration inventory, but no definition-node owner.
  `blueprint_refs.py search constant-extension` found three unrelated statement
  nodes. `blueprint_refs.py ancestor lem-dl-a1-constant-field-charts` returned
  `p-dl-a1-exact`, used in the new node's ancestry.

## Returned findings repaired

F1: `def-dl-a1-constant-extension-data` owns the seven landed definitions above,
with `existing: true`; the chart cites this node instead of the constant-extension
theorem. No definition is copied or changed.

F2: `lem-pur-coefficient-system-derived-comparison` is absent from the item's
`stmt_deps`. Its replacement node and module, and its direct import, are removed.
The landed coefficient-comparison record, NC's note and reducibility are retained.
The second-conjunct advisory is applied: the theorem quantifies over `∀ I`.
The local conjugacy clause retains the published stalks and Frobenius operators
and quantifies over all geometric-point embeddings; its isomorphism is existential.

## Maintenance overrides removed

The handoff's authoritative maintenance commits
`d77bd01fcb0aded1cc40aa47024a42b32947b0df` (redundant Galois-data import)
and `e6c3c9dd4506d42de1c826f59a7e8526cc16b35d` (slice sheafification instances)
supply the necessary dependency repairs on main. The current source returned by
`scompile.py --source Sheaf.Paper.AdicHeartPullbackFibres` no longer imports
`GaloisLisseRepresentationData`; it retains the monolithic
`GaloisLisseRepresentations` data. The saved relocation override therefore adds
no needed mathematical interface and is removed from the delivery. Its module
and copied correspondence node are retained only as `.bak` files under the
sandbox's `archive-maintenance-20261018`, outside the packet inputs.
The saved adic-fibre and slice-transpose overrides and copied records are already
absent. No dependency record is overwritten by this delivery. All legitimate
chart dependencies, including the shift-normalization definition, are retained.

## Second reading by NJ

The assigned worker performed this second pass with the node, chart module,
new definition-owner record and the current published constant-extension source open.
No other agent was started, as explicitly required by the dispatcher brief.

The ambient `MiddleExtensionCurve` retains finite type, separatedness and the
dense open; the explicit affine and relative-dimension-one assumptions give
the stated smooth affine curve. The `s` and compatible embedding binders cover
every boundary point and prescribed residue embedding. The chart keeps exactly
the residue subfield via `residue` and `embedding`, the rational lift via
`rational`, its residue isomorphism via `residueMap`, and the actual etale and
Cartesian maps via `etale` and `cartesian`. No connectedness of the original
curve is assumed. The restriction's carrier and Weil equations fix actual
inverse image with the m-fold Weil iterate. The normalized `higher` comparisons
cover exactly degrees zero and one; `degreeZero` and `boundary` retain ordinary
image and the delta square. `localImage`, `equalSize`, `localOpen` and `pure`
retain the two local Frobenius conclusions, relative residue degree and same
purity weight. The `∀ I` open-neighborhood conjunct and `DlOpenImageSuccessive`
retain arbitrary presentations, identity restrictions and successive restrictions.

F1's seven real definitions agree with the new owner node clause by clause:
new finite base, arithmetic pullback, original-base projection, distinguished
sheet, canonical geometric-fibre isomorphism and underlying heart carrier.
They remain the existing constructions in the landed module, with named proof
obligations rather than hollow data. F2's unused dependency override is absent.
The redundant dependency overrides are archived; all published dependency data
and node records are retained. No mathematical statement correction was made. Empty curves, empty/identity open restrictions,
zero sheaves, m=1 and nontrivial constant extensions remain included.

Self-check: the chart's `lean.statement` is verbatim from its module; the only
postponed chart theorem is `dlConstantFieldCharts`; explicit universes and
`autoImplicit false` are retained; every line fits 100 characters. The item
changes only `lean` and `stmt_deps`, adding the definition-owner node and landed
shift-normalization node. The chart retains its named postponed theorem with
its full thirteen-step proof docstring.

## Validation

The first dry run of the retained packet was run before any changes in this
retry. It reached the preliminary chart compilation without a chart diagnostic,
then continued checking the obsolete Galois override. An orphaned dry run from
the previous interrupted attempt was also found. Both obsolete-packet checks
were stopped before archiving the override; neither is claimed as a successful
final dry run. The final packet contains one new Lean file, the unchanged chart,
and the existing-definition ownership record. The chart signature is verbatim
in its node record, every line fits 100 columns, and its only `sorry` is the
whole proof of `dlConstantFieldCharts`. No theorem or definition was weakened.

Final single-file compilation, server preflight and delivery use only the
prescribed `scompile.py` and `deliver2.py` wrappers. Their results follow below.
Launcher tools, upstream sources and live library files were not edited.

Final packet check: `scompile.py NJ lem-dl-a1-constant-field-charts
lean/Sheaf/Paper/DlConstantFieldCharts.lean` returned exit 0 on 2026-10-18.
Both the sandbox file and library confirmation compiled without errors or
warnings, against current published dependencies and no sandbox overrides.
The chart SHA256 is
`1b79f07e89213805332218d6038ee32a0aad7382248d04f7b48fb039a29c3e5f`,
identical to the chart independently validated in the maintenance handoff.

`deliver2.py NJ lem-dl-a1-constant-field-charts --no-push` passed on
2026-10-18: `OK (dry run): commit 34ca399c42 passes the preflight and
compiles; nothing pushed`. The staged packet contains exactly the chart, its
node, the existing-definition owner node, and this report.
