## Worker report

The module `Sheaf.TraceFormula.LineProjChartPullback` states
`AlgebraicGeometry.Scheme.Modules.lineProj_chart_pullback` with `sorry`.
It adds seven real-data helper definitions for this node's specified pullback
and chart formulas. No mathematical statement or Lean source is changed. The definition node
`def-trf-line-proj-fraction-chart-data` now owns the eight plain definitions
from the landed atlas module, through an `existing: true` record. It replaces
`lem-trf-line-proj-affine-chart-atlas` in statement dependencies. The atlas theorem
remains a proof dependency; `def-sc-tensor-pullback-power-comparison` remains a
statement dependency for its normalized comparison.

### Hypothesis and clause correspondence

* Schemes and the arbitrary commutative square: `{W W' T T' : Scheme.{u}}`,
  `f`, `f'`, `h`, `g`, and `hsq : h ≫ f = f' ≫ g`. This is composition in
  categorical order. There is no `IsPullback`, flatness or finite-generation
  assumption on this square.
* Quasi-coherent commutative graded algebra: `A : RelativeProjAlgebra T`.
  This retained sheaf input has `algebra : QuasiCoherentAlgebra T`, homogeneous
  sheaves `piece`, `graded : GradedSheafAlgebra piece`, and the compatible
  decomposition. Its `affineData` is the existing bridge to canonical relative
  Proj, using the actual section rings. The input does not impose A_0 = O_T.
* Invertible line module: `L : W.Modules` and `[L.IsInvertible]`.
* Graded algebra map psi: `ψ n` is a map from the actual degree-n tensor
  pullback to `L.tensorPow n`. `hunit` and `hmul` are exactly the unit and
  multiplication equations on all open sections, as in the landed atlas.
  Additivity and O_W-linearity are carried by the sheaf-module morphisms.
* A' = g^* A: `A'`, the degreewise identifications
  `β n : A'.piece n ≅ (tensorPullback g).obj (A.piece n)`, and the existing
  coefficientwise `D : GradedAlgebraData.PullbackData g A.affineData A'.affineData`.
  `hD` requires that D.map is the actual map a ↦ a tensor 1 under these same
  identifications. Thus beta and the comparison D are not unrelated arbitrary
  maps or added flatness conditions: these binders express the stipulated
  identification with the pullback. D already includes graded ring laws,
  restrictions and degreewise scalar extension.
* L' = h^* L is always written as `(tensorPullback h).obj L`.
* Psi' is fixed by `hψ' : ψ' = lineProjPullbackMap hsq A A' L β ψ`.
  The helper has actual data: pull back beta, invert the normalized composition
  comparison for f',g, transport by hsq, apply the normalized comparison for
  h,f, pull back psi, and apply `boundaryPullbackPowIso h L n`.
  No choice from a bare existence theorem or arbitrary isomorphism defines psi'.
* G and G' are opens with `hG` and `hG'` explicitly identifying their underlying
  sets with the unions of positive-degree stalkwise surjectivity loci, using
  `TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}` and the actual degree maps.
  These equalities encode “write G and G' for”; they are not extra generation
  assumptions. The first conclusion is precisely `G' = h ⁻¹ᵁ G`.
* The coefficient and cover clause is `LineProjPullbackCoefficients`.
  It quantifies over every pair of affine base charts V,V' and every pair of
  affine source charts B,B', with their three mapping-inclusion conditions.
  It quantifies over every frame e via the existing `IsFreeGenerator e`.
  `lineProjPulledFrame` is the actual restriction of the section 1 tensor e;
  it is asserted to be a frame as well.
* `lineProjBaseSection ... a c` is c times the restriction of 1 tensor a,
  transported by beta inverse. For every n, a, alpha satisfying the original
  frame coefficient equation, its primed image has coefficient
  `(h.appLE ... α) * (f'.appLE ... c)`. Thus the asserted a tensor c formula
  refers to actual sections and the actual pulled-back map, not auxiliary
  coefficient homomorphisms. Taking n=0 also retains the tensor-unit case.
* The same predicate asserts that `G' ⊓ B'.1` is the union over d>0, a and
  their frame coefficients alpha of `B'.1 ⊓ h ⁻¹ᵁ W.basicOpen α`.
  `lineProjPulledBasicOpen` names precisely this last open. Because the scalar
  is uniquely determined by the frame, indexing by its coefficient equation
  is just a way of indexing by all a without making a noncanonical choice.
* The final conclusion quantifies over all maps q and q'.
  `LineProjSpecifiedMap` requires their factorizations through the existing
  generator-open charts, with `LineProjFractionFormula` for the given psi.
  The latter is the actual equation “scalar times psi(a)^m = psi(b)”. It is
  the previously landed homogeneous-fraction notion, not a second definition.
  Both generator opens must include into the stated domain by the displayed
  factorization of their ambient inclusions.
* The comparison c is exactly `D.relProjComparison`, whose equality with
  `D.relProjIsoPullback.hom ≫ pullback.fst ...` is already in the upstream
  BaseChange module. The conclusion supplies k with
  `k ≫ G.ι = G'.ι ≫ h` and `q' ≫ D.relProjComparison = k ≫ q`.
  Since G.ι is an open immersion, this k is precisely h restricted to G'.
* `LineProjCommonFractions` states that on every pulled-back generator chart
  there is a single map r to Spec of the existing degree-zero homogeneous
  localization, factoring both composites. It evaluates every `Away.mk` b/a^m
  by the equation r(b/a^m) h-sharp(alpha_a)^m = h-sharp(alpha_b), after restriction
  to that open. The denominator is a unit there, so this is exactly the stated
  quotient. It asserts both factorizations, not merely an abstract equality.
  All m ≥ 0 are included and b has degree m*d (written m • d).

### Dependencies read and used

Read the full recorded signatures/docstrings and the relevant implementations:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Modules.IsInvertible`,
  `tensorPow`, `tensorPowAddIso`, `tensorPowMulIso`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionComp`.
  This uses the uniquely section-normalized adjunction, not an arbitrary
  adjunction witness. Read its imported explicit `TensorPullback` construction.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `GradedAlgebraData.relProj`, `relProjι`, `relProjHom` and restriction interface.
* `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`:
  `RelativeProjAlgebra.affineData`, `grade` and the section-grading bridge.
  Its input is the retained `RelativeProjAlgebra` in `RelativeProjData`.
* `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `Away.mk`, `Away.mk_surjective`.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`:
  `GradedAlgebraData.PullbackData`, `relProjComparison`, `relProjIsoPullback`,
  `isPullback`, and the projection equality identifying their comparison.
* `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`.
* `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`.
* `Sheaf.TraceFormula.LineProjAffineChartAtlas`: `lineProjImage`,
  `lineProjElement`, `lineProjFramePower`, `lineProjGeneratorOpen`,
  `lineProjScalar`, `LineProjFractionFormula`, `LineProjChart`,
  `lineProjChartToRelative`, `exists_lineProj_affine_chart_atlas`.
* `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `boundaryPullbackPowIso` with its unit and recursive tensor comparison.
* Proof-only imports: `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`
  (`lem_nagata_affine_proj_scalar_extension`),
  `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
  (`exists_tensorPullback_affine_sections`),
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
  (`isQuasicoherent_pullback`), and `Mathlib.AlgebraicGeometry.Gluing`
  (`Scheme.Cover.glueMorphisms`, `hom_ext`).

The theorem docstring carries all five accepted proof steps and their node names.
All definitions contain actual terms; the sole postponed theorem is this item.

### Edge cases and source

Read `spaces-divisors.tex` Tag 0D2Z, including the preamble and part (3), and
`constructions.tex` Tag 01O9, including the preceding generator-open description
and its affine characterization (3). The arbitrary square and absence of
flatness/finite-generation assumptions match the source. Empty W or W', an
algebra concentrated in degree zero, and zero/nilpotent images give empty
positive-degree generation opens or empty generator charts; every formula still
makes sense. Zero-divisor denominators are inverted only on their basic opens;
regularity is never assumed. The cross-multiplied equation includes m=0 and
n=0 uses the canonical tensor-unit comparison. No intersection of affine opens
is required to be affine. Nonflat quotient maps and the identity square use the
same coefficient and normalized pullback formulas. One explicit scheme universe
u includes these cases; no independent smaller universe bounds test objects.

### Searches

All remote searches used the prescribed msearch.py with group N8 and this item.

* leanfinder: “Arbitrary pullback of positive degree generation loci of a graded
  algebra map into powers of an invertible sheaf and naturality of the fraction
  charts into relative Proj”. Eight results about Proj intersections and maps
  from global sections; no theorem with the arbitrary square and line module.
* loogle: `"AlgebraicGeometry.Proj", "pullback"`. Eleven results headed by
  `Proj.pullbackAwayιIso`, which is the intersection of two standard opens in
  a single Proj, not this pullback theorem.
* grep: `pullbackAway|base.change|scalar.extension`, restricted to
  `AlgebraicGeometry/ProjectiveSpectrum`. Eight matches, all the standard-open
  intersection construction and its uses in Proper.lean.
* leansearch: “Pulling back an invertible sheaf and a graded algebra homomorphism
  preserves the positive degree generation open and the canonical morphism to
  relative Proj”. Eight hits, including `Proj.fromOfGlobalSections_preimage_basicOpen`,
  for a ring map to global functions rather than a graded line-module map.
* rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `lineProjPullback|LineProjPullback` found no preexisting declaration.
  Broader generation/fraction/relative-Proj searches found the landed affine
  atlas and the existing RelativeGradedLineMap interface. The atlas is the
  precise sheaf-map input used here. The latter is a different input encoding
  and imports the parent `SpaceLineModuleProjMap`, so it is not imported here.
* Read `dag/lean_names_upstream.json` and searched the comparison/interface names;
  no existing theorem states this node. The withdrawn CompactObject example
  currently contains no declarations; its node record was read for format.

No `STATEMENT-DISPUTED` flag or statement correction is needed.

Validation: scompile.py compiled the module in both its sandbox and intended
library name with no errors and no warnings. The first attempt exposed a ring
section type inference ambiguity; explicit `@id` section types fixed it.

The dispatched brief assigns the independent second reading to the maintainer;
no other agent was started and this report does not claim an independent review.

## New nodes

`def-trf-line-proj-fraction-chart-data` owns exactly the existing declarations
`lineProjImage`, `lineProjElement`, `lineProjFramePower`, `lineProjGeneratorOpen`,
`lineProjScalar`, `LineProjFractionFormula`, `LineProjChart`, and
`lineProjChartToRelative` in `Sheaf.TraceFormula.LineProjAffineChartAtlas`.
Its source is Constructions Tags 01NK and 01O9: the generator-open definition,
the degree-zero fraction construction and the relative affine-chart inclusion.
The statement introduces f, A, L and the degreewise maps; it defines each of
these eight notions without asserting any theorem about existence or gluing.
The definition of image uses the actual tensor pullback section; the homogeneous
element uses the section-ring grading; frame powers include the unit at degree
zero; the generator open uses the existing generating locus; the scalar map
uses Gamma-Spec and the canonical open restriction; the fraction predicate
quantifies over every m and b and uses a cross-multiplied equality; the chart
is a morphism to the existing degree-zero localization spectrum; the relative
chart map is composition with the two existing chart inclusions.

The new search queries are retained verbatim in its `mathlib_searches`, with
the msearch results. LeanSearch returned graded tensor algebra operations and
`HomogeneousLocalization.Away.mk`; LeanFinder returned the global-functions
Proj construction and Proj structure-sheaf operations. None is the sheaf-map
chart interface. Mathlib grep found no occurrence of the eight names. Searches
of WeilConjectures and its names index found no matching definitions; Sheaf
contains precisely these definitions in the unchanged atlas module. DAG searches
and blueprint_refs searches found no definition node owning them: the atlas
node is a theorem node, and the P1 chart isomorphism and bundled relative graded
line map concern different notions. The existing declarations are reused, not
copied. Its record lists exactly the eight declarations requested in the return.

## Returned delivery repair

L's H2 return at immutable head `8fb30e07681b` identified that citing the atlas
theorem did not own its plain helper definitions. The saved packet's initial
dry run passed at `670bff3a8e7`, but that did not repair the independent review's
mathematical dependency-ownership objection. The new existing-definition node
above resolves it. The item now cites that definition node in stmt_deps instead
of the atlas theorem. The theorem remains in proof_deps and its proof-only use
is unchanged. No theorem statement, definition data, source or proof is changed.
Compared the saved item with the current shared-main node: the existing changes
are its Lean record and added statement dependencies only; this repair retains
them, replacing the newly added atlas-theorem dependency with the new definition
node. The delivery wrapper refreshes and rebases the packet against current main.

Self-check: read the eight source declarations and their docstrings, then
checked every use in the unchanged consumer module. None uses a choice from
the atlas theorem. Each declaration is accounted for by the new definition's
statement; its record does not claim the atlas theorem or unrelated overlap
predicates. The original edge cases (empty opens, degree zero, nilpotent
generators and nonflat maps) still apply. No independent agent was started;
the dispatched brief assigns the independent reading to the maintainer.

Repair validation: scompile.py compiled the unchanged consumer under both its
sandbox name (6.4 s) and library name (5.3 s), with no errors or warnings.
The consumer signature still matches its record exactly after whitespace
normalization. The new definition statement cites exactly its ten dependencies;
the item changes only stmt_deps and lean against current main.

The repaired-packet dry run first required separate bracket citations for the
two graded-algebra dependencies, rather than a shared comma-separated bracket.
Split those citations and reran the gate; no mathematical content changed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
