## Worker report

Delivered module: `Sheaf.Paper.ChartDncVectorFactors`, main declaration
`WeilConjectures.PurityFiniteSetting.ChartFactors.chart_dnc_vector_factors`.
All eighteen declarations are listed in the node record. The helper theorems state
geometric equations belonging to the node's specified constructions; every theorem
proof is `sorry`, with a source and natural-language proof. Definitions have actual
data. No statement correction, new node, or dependency replacement is needed.

Source read: current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md`, Steps 1--4,
together with all five steps of the item's DAG proof. The main docstring spells
out the five-step argument, including the two exceptional-normalization identities
needed to identify the pasted comparisons with the specified canonical maps.

Hypotheses, one by one:

- `P : PurityFiniteSetting.{u}` is the recorded finite-field and coefficient datum:
  its field is the fixed algebraic closure of a finite field, its coefficient prime
  differs from the characteristic, and `P.level_pos` says n >= 1.
- `_hE : P.extension = ⊥` specializes E to Q_ell. The coefficient used everywhere is
  the recorded quotient `P.Coefficient`, the standard size lift of O_E/(varpi_E^n),
  hence the prescribed finite coefficient ring in this specialization. It is not
  a freely supplied ring. The positive exponent is `P.diagonalExponent = ell^n`.
- `{U Y : Scheme.{u}} [IsAffine Y]` supplies the schemes and affineness of Y.
  There is no affineness hypothesis on U.
- `aY : Y ⟶ Spec (.of P.field.k)`, `[LocallyOfFiniteType aY]` and
  `[QuasiCompact aY]` say Y is finite type over k. Affineness supplies its
  separatedness over k; the composition h followed by aY supplies U's structure.
- `d : ℕ` includes zero. `[SmoothOfRelativeDimension d h]` is smoothness of
  pure relative dimension d, not merely a bound on the dimension.
- `[IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]` render the three
  remaining morphism conditions. U is therefore finite type over k; no additional
  compactifiability or Noetherian assumption is imposed on the theorem.
- `e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y`, `[Etale e]`, and
  `w : e ≫ (AffineSpace ... Y ↘ Y) = h` render the etale Y-chart, with the
  usual d-coordinate affine space. The ULift changes size only.

Objects and clauses, one by one:

1. W and W_A are Mathlib `pullback h h` and `pullback p p`, with
   `pullback.fst` and `pullback.diagonal`. `selfMap` is `pullback.map` with e
   on both factors, so it is the actual e times e, not a chosen map.
2. The source comparison a is `source`. Its ordinary form `sourceOrdinary`
   factors through H = W_A times_A U: `sourceLift` is (1,e), etale over U,
   and the second comparison is inverse smooth exceptional base change along e.
   It is defined by normalized exceptional adjunction, not by choosing an
   isomorphism of the endpoint objects. For the node's O and i, locality gives
   R_r = R_i R_(r|O) as maps into C(p_U,Delta_U), so inverse locality for r
   is inverse locality for r|O followed by open restriction to O. Exceptional
   composition and its smooth-base-change compatibility identify the resulting
   composite with exactly the node's comparison for q=(e times e)|O. Thus no
   choice of a smaller neighbourhood or arbitrary comparison is introduced.
   This factorization avoids storing an otherwise unused copy of O or its ideal.
3. The normal cones are literally the diagonal-kernel `normalCone` constructions,
   with `Scheme.Hom.normalConeProj` and `normalConeZeroSection`. `idealCondition`
   supplies the actual ideal inclusion for e times e; `deformation` applies
   `Scheme.IdealSheafData.deformationSpaceMap`. `normalMap` is its zero-fibre
   map by the fixed normal-cone pullback universal property. On rings it fixes t
   and sends a/t to e*a/t. Thus on degree one it sends [a] to [e*a], i.e. the
   actual conormal map, whose dual is de. `normalGeometry` states its Cartesian
   square and zero-section equation. This is the specified actual normal-bundle
   identification, with no assumed arbitrary bundle isomorphism.
4. The normal comparison b is `normal`: inverse `Dnc.sectionBaseChange` for
   that actual square, followed by the canonical ordinary/pro-etale comparisons.
   This is the inverse exceptional exchange on the normal bundle pulled to zero.
5. Delta_h and Delta_p inline the unique normalized choice
   `(Dnc.existsUnique_dncInvariance ...).exists.choose` at h and p.
   This uses the already cited DNC theorem directly; `chartDiagonalDelta`
   and the chart-normalization theorem are not used.
   Its defining DNC family has x_i=t*u_i, so u_i=x_i/t and the standard-section
   normalization is fixed. No scalar or sign is a parameter of the statement.
6. `beta` uses `chartNormalModel`, whose value is fixed by the relative-Spec
   and homogeneous Rees normalization, to pass from the actual cone to Spec Sym
   of the conormal module. It then uses `bundleOrientation`, which by definition
   is the inverse of `bundleSectionAdjoint`, the actual integration transpose
   restricted to zero. This is not a re-use of the diagonal orientation whose
   chart compatibility is being stated. The whole map is transported by nu*.
   Its endpoint is definitionally `P.diagonalTwist U d`, the established model
   of Lambda_U(d)[2d]. This uses the ordinary trace rather than an unspecified
   pro-etale purity isomorphism.
7. `tate` is the canonical base-coefficient pullback followed by the nu* pullback
   comparison. It supplies the target identification in the second equation.
8. The first conjunct of `Conclusion` is exactly
   delta_h.hom ≫ b.hom = a.hom ≫ e*.map delta_p.hom.
   The second is beta_h.hom = b.hom ≫ e*.map beta_p.hom ≫ tate.hom.
   In Lean, composition is written in diagram order, giving precisely the two
   displayed equations in the node. These are equalities of actual morphisms in
   the specified small pro-etale derived categories, not equality of iso classes.
9. The final conjunct is `FrameIndependence P d h aY N t`, an equation
   involving `beta_h` itself, not a restatement of affine trace invariance.
   It sets `F = ConormalGradedAlgebra.piece (pullback.diagonal h) 1`, the actual
   conormal module of the diagonal, and quantifies each open `W : U.Opens`,
   each module frame `f : VectorBundleZeroSection.Trivialization U d F W`,
   and `G : Aut (F.restrict W.ι)`. Thus G is GL of the conormal module on W;
   the changed frame is literally `G ≪≫ f`. This covers the pulled-back frame
   from the etale chart and every further linear change, as well as restrictions
   to smaller opens. `IsNoetherian W.toScheme` is constructed from the inherited
   local Noetherian and compact structures, not assumed.
   The left side pulls back `(beta ...).inv`, passes by
   `normalBundleComparison` to the fixed relative-Spec model of N_U, then uses
   `bundleFrameSectionMap ... (G ≪≫ f)`, the canonical exceptional mate for
   that actual frame. The right side uses canonical Tate pullback and the
   same `affineSectionAdjoint` for every G. Both sides are actual morphisms
   on the pro-etale site of W, via `Dnc.pullComparison` and nu*. Taking G=1
   gives the original frame; arbitrary G gives the identical affine adjoint
   after the changed-frame identification. Inverting gives precisely the
   frame independence of beta_h used in the second chart equation.
10. The quantifiers on compact-support normalization N, root-line transport t,
    and the normalized ordinary P1 datum D specify presentations of the canonical
    functors and Kummer trace already used by the dependencies; none assumes the
    conclusion or an arbitrary orientation. The equations hold for every such
    normalized presentation. The d=0 standard normalization is inherited from
    the very same ordered empty trace, normalized DNC, and empty tensor product.

Dependency declarations used (module names are prefixed by Sheaf unless shown):

- `Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `P.Coefficient`, `P.noetherian`; the recorded conventions are used directly.
- Mathlib pullbacks and `AlgebraicGeometry.AffineSpace`, its projection and
  `smoothOfRelativeDimension_over`; Mathlib `IsSeparated`, `Etale`,
  `SmoothOfRelativeDimension`, `QuasiCompact`, and `LocallyOfFiniteType`.
- `Paper.PuritySectionInvariantIntrinsic`:
  `P.sectionInvariantFinite` is the intrinsic recorded section notion;
  `Paper.PurityDncComparisons`: `Dnc.sourceEtale`, `Dnc.sourceComparison`,
  `Dnc.normalEtale`, `Dnc.normalComparison`, `Dnc.pullComparison`, and
  `Dnc.sectionBaseChange` give its already established fixed-ring/site realization.
  `Paper.PurityDncInvariance`: `Dnc.existsUnique_dncInvariance`.
- `Paper.PurityNormalBundle`, `Paper.PurityNormalProjection`:
  `Scheme.Hom.normalConeProj`, `normalConeZeroSection`, `normalConeData`;
  the actual extended-Rees ideal-sheaf `deformationSpaceMap`,
  `normalConeToDeformationSpace`, and
  `Scheme.Hom.isPullback_normalConeToDeformationSpace` are reused.
- `AlgebraicGeometry.ConormalAlgebraFlatBaseChange`:
  `ConormalGradedAlgebra.existsUnique_baseChangeMap`, used in the natural-language
  proof identifying the actual Rees zero-fibre differential.
- `Paper.DiagonalDncChartNormalization`: `chartSectionEtaleRestriction`, `chartDiagonalNormalBundle`,
  `chartNormal_model_exists`, `chartNormalModel`. Only these canonical construction
  helpers are used; `diagonal_dnc_chart_normalization` and the affine-chart
  compatibility conclusions are not used as assumptions or definitions.
- `Paper.FiniteRingSectionDeformation`: `bundleOrientation`, `bundleSectionAdjoint`
  and its isomorphism theorem interface; these realize inverse ordinary integration
  and have target `Etale.affineLinearBaseCoefficient`. `bundleFrameSectionMap`,
  `affineSectionAdjoint`, `standardZero`, and `standardZero_over` give the actual
  frame exceptional mate and affine adjunct in FrameIndependence. The proof uses
  `bundleOrientation_frames` for the changed conormal frame.
- `Paper.FixedFinitePositiveCoefficientTwist`: `P.diagonalExponent`,
  `P.diagonalExponent_annihilates`, `P.diagonalExponent_isUnit`,
  `P.diagonalTwistEtale`, `P.diagonalTwist`, the fixed-ring positive finite-twist
  interface of the recorded coefficient-twist dependency.
- `Paper.VectorIntegrationSiteComparison`:
  `Etale.vectorIntegrationBaseCoefficientPullback` and the ordinary/pro-etale
  integration comparison, used to identify the actual transported transpose.
- `Paper.CartesianCoefficientTwists`: the prescribed canonical Tate pullback;
  `ProEtale.comparisonUpperStar` and `ProEtale.upperStar` are the established
  exact comparison and derived pullback, retaining the site's universes.
- `AlgebraicGeometry.AffineSpaceLinearTraceInvariance`:
  `affineTraceLinearMap`, `affineTraceProjection`, `Etale.affineLinearTraceAction`,
  `Etale.affineTraceCounit`, and its linear-invariance theorem.
- Proof imports: `SecSmoothPurity.FiniteEtaleDualizingNormalization` (parts 2--3),
  `Paper.CohomologicalSmoothnessTheorem`, and
  `AlgebraicGeometry.VectorTraceGeometricDescent`. The recorded proof-only chart
  domain, differential, and section-restriction coherence nodes have no usable
  own modules yet; their statements and proof content are cited in the docstring.
  Their geometry needed for data construction is stated here as the named helper
  theorems, not added as hypotheses of the main theorem.

Added statement dependencies are already landed nodes with lean records:
`def-pur-diagonal-dnc-chart-data`, `def-pur-finite-ring-section-data`, and
`lem-trf-finite-ring-section-deformation`. They own the existing canonical
construction helpers just listed. A traversal of both statement and proof edges
found no dependency path from any of these nodes back to this item. No theorem
about this item's two chart identities is assumed.

Edge cases checked before and after writing:

- d=0: no positive-rank assumption occurs; the coordinate index is Fin 0,
  the coefficient tensor is empty, and the established trace and DNC normalizations
  are identity data. GL_0 also gives the identity action.
- Empty U: every construction is still a scheme/site construction; invertibility
  in the zero global-section ring is covered by the recorded isUnit theorem.
  No chosen rational point, nonempty cover, or trivializing frame is required.
- Non-affine U of finite type: there is no `[IsAffine U]` in the statement or
  constructions. The normal cone and its model use sheaves and relative Spec.
- Open chart G_m -> A1 and the degree-two etale map on G_m in characteristic
  different from 2: the latter has an extra antidiagonal component in Z. The
  actual normal differential scales by 2x, not by an arbitrary unit or identity;
  the Rees-induced map retains this factor. The global locality factorization
  agrees with restriction removing the antidiagonal near the diagonal.
- No extra equality between site and coefficient universes is imposed: schemes
  have universe u, fixed coefficients u+1, and the actual small pro-etale site.

Searches performed for exact reuse:

- msearch leanfinder: "Etale coordinate chart compatibility of normalized deformation
  to the normal cone and inverse vector bundle integration trace": eight hits on
  ordinary etale polynomial presentations; no matching derived equation.
- msearch loogle: "AlgebraicGeometry.Etale": twelve definitions/stability hits;
  no matching comparison statement.
- msearch grep: "dncInvariance|vectorBundlePurity|integrationTrace|normalCone.*etale":
  zero Mathlib hits.
- msearch leansearch with the same natural-language chart query: eight hits on
  topological VectorBundleCore/trivializations; no matching statement.
- rg across lean/WeilConjectures and lean/Sheaf for the item id, dnc/chart,
  integration, and normal-map names: found the reused constructions above,
  but no theorem for these two specified equations for arbitrary non-affine U.
  The older affine-chart mate coherence and diagonal-normalization theorem do
  not have the full statement, so existing:true would be incorrect.
- tools/blueprint_refs.py search "diagonal chart": zero hits; DAG searches
  identified the already landed helper-owner nodes, reused rather than copied.

Validation of the original packet: scompile.py compiled both the isolated sandbox
module and the actual library module cleanly (12.7 s and 12.6 s). The initial repair
dry run also passed mechanically; the mathematical defects still required changes.
Repair compilation and final delivery checks are recorded below. The node JSON signature
is extracted verbatim from the theorem, and the original statement and proof are
unchanged. There is no STATEMENT-DISPUTED finding.

## Second reading by Q126

This is a second pass by the same dispatcher-started worker, not a claim of an
independent second worker: the human brief forbids starting other agents and says
that the maintainer independently reviews the delivery.

With the node, current blueprint Steps 1--4, and module open, checked every
hypothesis against the list above. In particular E=Q_ell is an explicit hypothesis,
n>=1 is carried by P, finite type and separatedness of h are retained, and only Y
is affine. Checked both equations in diagram-order Lean composition: a goes from
source_U to e*source_A, b from normal_U to e*normal_A, and beta from the normal
section to the positive twist; the inserted tate comparison has the required target.
Checked that the Rees and normal constructions use e times e and the actual ideal
inclusion, rather than an unspecified isomorphism. Checked the source locality
factorization against the node's O/q definition using locality composition and the
exceptional-normalization clauses, so it is the specified comparison. Checked
the DNC unique normalization and bundleOrientation's definition as
inverse actual adjoint, rather than the chart orientation itself.

During this pass, rejected an unnecessary second coefficient-descent factor in
beta: the existing bundleOrientation target already is the ordered shifted Tate
coefficient, definitionally the required endpoint. Removed that factor before the
final clean compile. Also corrected the namespace of affineTraceLinearMap to its
actual AlgebraicGeometry namespace. No mathematical hypothesis or node statement
changed. Checked d=0, empty U, non-affine U, and the noninjective etale chart example
again, and checked that all helper-node additions are acyclic and use existing data.
Corrected the sourceLift_geometry proof explanation to obtain quasi-compactness
from the closed graph and quasi-compact source projection; that helper itself does
not assume a field base. The first delivery dry run passed preflight and compilation.


## Returned-head repair (2708a099fb69)

Compared the saved packet and the current shared node: the saved changes were its
Lean attachment and four added statement dependencies; no statement or proof edits.
The current main does not contain ChartDncVectorFactors.lean, so no landed consumer
interface is overwritten. The first required dry run of the saved packet returned
OK at dda47ff8bc7. It did not address the independent mathematical return, so the
following are substantive repairs, not an unchanged re-push.

H2: removed `lem-pur-diagonal-dnc-chart-normalization` from the added statement
dependencies. Both delta maps now inline the unique normalized choice from the
already cited `thm-pur-dnc-invariance`. No private copy or additional owner node is
needed. The remaining chart helpers are owned by
`def-pur-diagonal-dnc-chart-data`. Kept `lem-trf-finite-ring-section-deformation`:
its isomorphism theorem is genuinely used by `bundleOrientation`, as the return
explicitly confirmed.

H3/H5: removed the unrelated affine-trace conjunct. The new FrameIndependence
clause contains beta_h, the actual conormal module F, every local frame f and
its change by every G in Aut(F restricted to W). Its two sides are the pulled
inverse beta in these frame coordinates and the fixed affine integration adjunct.
The canonical bridge normalBundleComparison is the original beta prefix factored
out, before any integration map; beta is still that bridge followed by the inverse
actual bundle integration transpose. FrameIndependence is therefore not a tautology
introduced by defining its comparison from beta. Its proof uses the existing
bundleOrientation_frames theorem on G followed by f, plus naturality of the
ordinary/pro-etale pullback comparisons. Every new definition has real data and
belongs to this node; no new theorem or sorry was introduced.

Second reading of the repair by Q126: opened current blueprint chart proof Steps
1--4, the node, and the final module. The hypotheses and the first two equations
retain their original types, directions, source comparison, Rees normal map and
Tate normalization. The conormal rank is supplied by chartDiagonalNormalBundle;
f is an isomorphism of the restricted conormal module with the standard free
module, not a scheme isomorphism with unspecified linear action. Precomposing f
with G gives every invertible linear frame change, and G=1 covers the unchanged
frame. The frame comparison is the actual exceptional mate, while its fixed
right-hand affineSectionAdjoint transposes the actual affineTraceCounit. Thus
the new equation expresses the claimed frame independence of beta_h itself.
For d=0 the conormal is rank zero and its frame action is the unique one; for
empty W and empty U all constructions remain defined. Non-affine U is covered
by all its frame opens, with no affineness assumption on U. Universe u and
coefficient universe u+1 are unchanged. No source-based statement correction,
new DAG node or dependency replacement is needed.

Additional repair searches: msearch leanfinder on "Frame independence of zero
section inverse vector bundle integration adjoint on the conormal sheaf" returned
eight differential-topological local-frame hits, no matching derived equation.
msearch loogle "CategoryTheory.Aut" returned its standard categorical automorphism
group and iso equivalence, reused for GL of the module. msearch grep
"bundleFrameSectionMap|bundleOrientation_frames|normalFrame" returned two unrelated
Mathlib local-frame text hits. rg in lean/Sheaf found the existing finite-ring
frame mate and frame-normalization theorem, which are reused; rg in
lean/WeilConjectures and lean/Sheaf found no declaration of normalBundleComparison
or this FrameIndependence predicate. The prior full searches remain applicable.

Final repair validation: scompile.py compiled the isolated sandbox in 10.5 s and
the actual library module in 11.4 s, with no errors or warnings. The main signature
is extracted verbatim into the node, all 18 declarations are listed, and the only
node changes are lean and three added landed statement dependencies. All six
theorems retain sorry proofs; every definition has actual data.
