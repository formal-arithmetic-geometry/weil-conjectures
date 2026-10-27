## Worker report

This delivery states ordered affine-space integration transport on the ordinary
constant-module derived categories. It keeps the actual supported-Kummer projective
trace, its restriction by the open counit, and the independent ordered counit.
No pro-etale trace is defined by transporting an ordinary trace.

Source read: main-20261015, sec-smooth-purity/sk-prop-an/
lem-amb-affine-space-top-trace.proof.md, paragraphs 2--3. Paragraph 2 identifies
the restricted projective-line trace with the affine-line composite counit;
paragraph 3 uses projection on the compactifications and induction over ordered
coordinates. The node records the additional site-transport argument explicitly.

The hypothesis/clause correspondence is as follows.

- The finite field, coefficient closure, finite subextension, and positive level
  are `P : WeilConjectures.PurityFiniteSetting`. The coefficient used by the existing
  finite-site interfaces is `Scheme.finiteTateCoefficient P.coefficients.l
  P.extension (P.level - 1)`: its quotient level is `(P.level - 1) + 1 = P.level`,
  since `P.level_pos` states positivity. This is the standard sheaf-universe lift.
- The finite-type base is `S`, its actual map `a` to `Spec P.field.k`, and
  `[LocallyOfFiniteType a] [QuasiCompact a]`. There is no absolute separatedness
  hypothesis. `r : Nat` denotes the node's positive exponent minus one; `hA`
  is exactly the annihilation equation by `ell^(r+1)`. There is no ramification
  divisibility condition and no flatness over the Kummer coefficient ring.
- The existential Noetherian witness `hN` and invertibility witness `hS` are
  conclusions from these data. Subsequent expressions use those proof witnesses
  to access the existing interfaces. Proof irrelevance makes their choices immaterial.
- `LineComparison` is the explicit hypothesis on every coordinate-line projection,
  at its constant input. It uses `orderedIntegration` at dimension one, whose definition is precisely
  inverse `lineSiteComparison` followed by the independent `lineCounit` (the
  identity rank-zero compositor cancels), and the ordinary trace at dimension one.
  HEq avoids elaborator expansion of the canonical dimension-one right-object
  identification; the objects are definitionally the same.
- `Model` enumerates affine tower schemes, the standard projective completion,
  iterated projective-line completions, and Zariski open restrictions. The first
  clauses of `Conclusion` assert Noetherianity and qcqs of the morphisms among
  these models. This includes every compactified projection used in the tower.
- `FiniteInput` asserts bounded constructibility on both sites and a common
  finite Tor interval. Applied to every ordered Tate right input over the models,
  this covers the shifted lines and their successive pulled-back tensor coefficients.
- The ordered-trace equality uses the existing `orderedIntegration` and the
  normalized ordinary `affineTraceCounit`; it holds for every dimension, hence
  every tower prefix.
- `etaleCompact` is the ordinary ordered compositor followed by the published
  compactification comparison. `proTrace` represents the already defined independent ordered trace in the
  coordinates of an arbitrary chosen compactification. `etaleTrace` does the
  same for the ordinary trace. Their equation uses precisely the inverse of
  `compactSupportSiteComparison`, namely the node's B.
- The completion-change clause uses the published common-refinement map
  `coherenceCompactificationChange`. The additional refinement clause uses
  `properTransportRefinement` for every actual proper refinement.
- `OpenCompatibility` spells out the restriction square using the published
  affine compact-support exchange, normalized right-object base-change map,
  canonical inverse-image comparison, and constant-unit pullback.
- `IsIso` is asserted for the actual traces in both sites at every completion;
  this is the stated concentration isomorphism as derived objects.
- The final heterogeneous equalities express the identity trace and identity
  source comparison at dimension zero. They include the empty scheme.

Dependency interfaces read and used include:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`; the existing
  `affineTraceTower` uses successive standard affine lines and its published
  `affineTraceAffineSpaceIso` identifies the result with affine d-space.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, whose counit
  formula is the existing ordered adjunction construction.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` and its construction modules:
  `Etale.affineTraceCounit`, `Etale.affineTraceLeft`, `Etale.affineTraceRight`,
  `Etale.affineTraceCompactSupportComparison`, `Etale.affineTraceExchange`.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`:
  `Etale.projectiveLineTraceTransport`, `Etale.projectiveLineTraceDatum`.
- `Sheaf.Paper.FiniteTateSiteDescent`: `Scheme.finiteTateCoefficient`,
  root-projection-normalized finite Tate descent.
- `Sheaf.Paper.FiniteSiteCoordinates`: `comparison`, `unit`, `pullback`,
  `pullbackUnit`; its Tate comparison fixes the inverse-limit twist coordinates.
- `Sheaf.Paper.ProEtaleProjectiveLineTrace`: `projectiveTrace`, defined by
  the supported-Kummer biproduct decomposition and second projection.
- `Sheaf.Paper.ProEtaleAffineLineCounit`: `lineCounit`, `lineLeft`,
  `infinityCartier`; the open-extension counit occurs in the defining arrow.
- `Sheaf.Paper.FiniteSiteTensorProjection`: coefficient-first `projection`
  and canonical tensor/pullback comparison.
- `Sheaf.Paper.ProEtaleProjectiveCoefficient`: `projectiveRightComparison`.
- `Sheaf.Paper.ProEtaleProjectionIntegration`: `projectiveEpsilon`, uniquely
  characterized by inverse proper projection followed by tensor of the trace.
- `Sheaf.Paper.ProEtaleOrderedIntegration`: `towerCounit`, `towerSiteComparison`,
  `orderedIntegration`, and `rightTower_plus`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, composed from the fixed proper mate and open
  comparison; `FixedComparisonDirectImageMate` and `ProEtaleExtensionZeroComparison`
  are imported as recorded dependencies.
- `Sheaf.Paper.CompactSupportSiteCoherence`: the actual completion-change and
  refinement maps, with the composition and restriction coherence proof tools.
- `Sheaf.Paper.FiniteTorAmplitudeSites`,
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`:
  the existing constructibility and Tor-amplitude predicates.

The remaining recorded statement and available proof dependency modules are
imported with the required visibility; the source records for intrinsic module
categories and scalar operations are not replaced by private definitions.

Edge cases checked: dimension zero and one; empty and disconnected bases;
a finite-type base that is not separated; positive coefficient level one;
an arbitrary annihilating exponent; ramified coefficients where the ramification
index does not divide the level. The same small-site object/morphism universes
are retained; no equality of those universes is imposed.

Searches performed (the sandbox search log records the remote searches):

- LeanFinder: "comparison between etale and pro-etale ordered affine space
  compact support trace integration" returned eight unrelated algebraic/topological
  results, no trace-transport statement.
- Loogle: "AlgebraicGeometry.Etale.affineTraceCounit,
  AlgebraicGeometry.ProEtale.compactSupportSiteComparison" reported unknown
  identifier for the project declaration; it supplied no Mathlib match.
- Mathlib grep: "orderedIntegration|towerSiteComparison|affineTraceCounit"
  returned zero hits.
- LeanSearch: "etale proetale comparison affine space trace compact support"
  returned algebraic etale and small-etale-site declarations, no match.
- Project ripgrep for the item id, `affineTowerIntegrationSiteTransport`, and
  `AffineTowerTransport` found no existing theorem in WeilConjectures or Sheaf.
  Existing lower-level traces and canonical comparison maps were reused.

No statement correction, new DAG node, or dependency repair is intended.
The only postponed theorem is `affineTowerIntegrationSiteTransport`; its docstring
contains the eleven-step proof plan of the node. Helper definitions contain real
canonical data.

The item adds two already landed statement dependencies:
`def-pur-chosen-compactification-compositors` and
`def-sf-refinement-comparison-isomorphism`. They own the actual common-refinement
and proper-refinement arrows named by the conclusion. No dependency
node is changed. The completion and relative-projective constructors in `Model`
include projective-line completions over every affine prefix and arbitrary chosen
compactifications over S. In addition to the ordered right-input clause, the pure
shifted-Tate clause explicitly covers each shifted rank-one input on these models.

The dimension-one line hypothesis is definitionally the originally specified
restricted counit with its canonical B. It is not an assumption about higher
integration maps and supplies no coefficient-wise compatibility assumption.
The only theorem proof in the delivery is `by sorry`; all other declarations are
concrete definitions or propositions organizing the statement.

Validation: the final module compiled cleanly through scompile.py in both sandbox
and named-library modes (12.4 and 10.9 seconds, respectively). The prescribed
`deliver2.py --no-push` completed with OK: all server preflight checks and the
per-file compile passed. Read Stacks sites-cohomology.tex
`lemma-j-shriek-and-tensor` and `remark-compatible-with-diagram`, and
proetale.tex `section-comparison`: these are exactly the open tensor formula,
projection/base-change compatibility, and canonical site comparison used in
the proof docstring. No global build or direct repository mutation was run.


## Returned delivery repair

L returned immutable head `c55c6e3c59a9` for H2: the completion-change clause
uses the plain definition `AlgebraicGeometry.ProEtale.coherenceCompactificationChange`,
not a choice from the theorem `compactSupportSiteCoherence`. Replaced the item's
statement dependency `lem-pur-compact-support-site-coherence` with the already
landed definition node `def-pur-chosen-compactification-compositors`, whose
`lean.declarations` owns that exact definition in
`Sheaf.Paper.CompactSupportSiteCoherence`. Reading its definition confirms the
common-refinement composite: inverse `properTransportRefinement` to the first
compactification followed by `properTransportRefinement` to the second.
Retained `def-sf-refinement-comparison-isomorphism` for the explicit
`properTransportRefinement` clause. The theorem node remains a proof dependency
for the coherence equations used in the proof plan. No proof dependency, informal
statement, theorem signature, or Lean source is changed by this repair.

Self-check: the completion-change conjunct of `Conclusion` uses precisely the
definition owned by the replacement node; the adjacent proper-refinement conjunct
uses the retained definition node. All hypothesis and clause correspondences and
edge cases above remain valid. The saved packet first passed the prescribed
initial dry run at `1f0a7701b83`; this pass alone did not resolve the review finding.
The repaired packet is validated again by the required server compile and dry run.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
