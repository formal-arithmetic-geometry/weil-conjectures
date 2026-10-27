## Worker report

Repair of immutable returned delivery cfe75797505b, H2. The three accepted theorem
signatures remain unchanged: AlgebraicSpace.nodal_chart_locality,
AlgebraicSpace.nodal_yoneda_iff, and nodal_geometric_point_chart_locality, in
Sheaf.AlgebraicGeometry.SpaceNodalChartLocality. Every theorem proof is sorry;
its docstring carries the matching portion of the item's five-step proof.

The scheme predicate and ordinary-node helpers now belong to the same-delivery
Sheaf.AlgebraicGeometry.SchemeNodalRelativeCurve, owned by
`def-sfb-scheme-nodal-relative-curve`. This uses the full scalar-compatible
construction expressly allowed by the return; it does not use IsNodalRelativeCurve.
Its definitions have real data. The old redundant ring-only conjunct is removed;
flatness, local finite presentation, pure dimension one, and the closed-point
completed Ω-algebra condition are written directly. No mathematical condition of
the accepted consumer changes.

Sources read: Stacks curves.tex Tag 0C59 (lemma-nodal-family), 0C5A
(definition-nodal-family), and 0C57 (lemma-node-etale-local);
spaces-more-morphisms.tex Tag 0DSG(4)--(7), 0DSF, and the paragraph and definition
preceding them. Read the recorded definition nodes and full Lean definitions of
completedLocalScalarMap, OpenSubspace and LocallyOfFiniteType.

Clause correspondence, including every hypothesis and conclusion:

- `{S : Scheme.{u}}`, `X Y : AlgebraicSpace S`, and `f : X ⟶ Y` are arbitrary.
  The site, geometric fields Ω and schemes use the same explicit u as the recorded
  space interface. No smaller independent test universe makes a condition vacuous.
- `IsNodalRelativeCurveWithScalars f` is Flat f and LocallyOfFinitePresentation f,
  followed by every Ω : Type u with Field and IsAlgClosed instances and every
  `g : Spec Ω ⟶ B`. The actual `Limits.pullback f g` is required to have
  `Scheme.IsPureDimension ... 1`.
- Every point x with no smooth open neighbourhood satisfies IsOrdinaryNodeOver.
  This is `x ∈ closedPoints D` and a nonempty type of Ω-algebra equivalences
  between the actual maximal-ideal AdicCompletion of D.presheaf.stalk x and
  MvPowerSeries (Fin 2) Ω / Ideal.span {X 0 * X 1}. The completion algebra is
  `(b.completedLocalScalarMap x).toAlgebra`; the target uses its usual quotient
  algebra. Thus neither the coefficient map nor the isomorphism is arbitrary.
- `IsNodalRelativeDimensionOne` is the existential diagram of U,V : Over S,
  representable étale a and b, surjective a, and h : U ⟶ V with
  `a ≫ f = yoneda.map h ≫ b` and IsNodalRelativeCurveWithScalars h.left.
- `NodalAtlasCriteria` equates this with the universal diagram condition, with
  no surjectivity assumption, and separately with existence of a surjective
  étale target scheme atlas b having nodal `pullback.snd f b`, and a surjective
  étale source scheme atlas a having nodal `a ≫ f`.
- The second conjunct of nodal_chart_locality is stability under every space
  Y' and every g : Y' ⟶ Y, on the canonical presheaf-pullback second projection.
- Its last conjunct quantifies over every OpenSubspace X, uses its actual inclusion
  A.val.ι, states preservation on restriction, and states the same three atlas
  criteria for the restriction, even when f itself is not nodal.
- nodal_yoneda_iff gives exact agreement on scheme morphisms.
- nodal_geometric_point_chart_locality has Ω algebraically closed, arbitrary
  locally finite type b : C ⟶ Spec Ω, an étale e : D ⟶ C and any y : D.
  It equates smooth relative-dimension-one open neighbourhoods at e(y) and y,
  separately equates ordinary nodes, and, if either point is closed, gives both
  closedness assertions and a nonempty type of Ω-algebra completion equivalences.
  It further gives a bijective ring map ehat preserving canonical scalars and
  whose reductions modulo every power of the maximal ideals agree with
  e.stalkMap y. Thus the comparison is the induced map. Two charts are compared
  by their scheme common refinement as explained in the proof docstring.
- No properness, connectedness, nonemptiness, global purity, quasi-compactness,
  separatedness or Noetherian assumption on the spaces is added. Local finite
  type over Ω is only the pointwise clause's scope, already in proof step 5.

Definition declarations and modules reused:

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsEtale, IsSurjective,
  IsRepresentableWith, defined by representable scheme tests.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat; .FinitePresentation:
  LocallyOfFinitePresentation; .Smooth: Smooth, SmoothOfRelativeDimension;
  .Etale: Etale; .FiniteType: LocallyOfFiniteType.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and snd.
- Sheaf.AlgebraicGeometry.PureDimension: Scheme.IsPureDimension.
- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic:
  IsAlgClosed; Mathlib.Topology.JacobsonSpace: closedPoints.
- Mathlib.RingTheory.AdicCompletion.Basic and .Algebra: AdicCompletion, evalₐ;
  Mathlib.RingTheory.MvPowerSeries.Basic: MvPowerSeries and its variables.
- def-trf-completed-local-scalar-map owns Scheme.Hom.completedLocalScalarMap in
  Sheaf.AlgebraicGeometry.NodalPointEtaleLocality. The actual composite of constants,
  pullback, germ and completion was reread; no theorem is needed to define it.
- def-a1-space-open-subspace owns AlgebraicSpace.OpenSubspace in
  Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers supplies the recorded
  fibre-product closure, base change of étale coverings and scheme representability.

The theorem-module imports for source locality and node locality remain as proof
inputs. Their theorem nodes remain in proof_deps, not stmt_deps for their helper
notions. The currently unstated proof inputs remain in the DAG and proof docstrings.
The legacy source-locality proof module forces the consumer to retain legacy imports;
the new definition module itself uses the current module format.

Edge cases checked: empty sources and fibres, empty atlases of empty spaces,
nonsurjective vertical maps in the universal test, disconnected spaces,
characteristic two, and mixed-dimensional ambient schemes in the pointwise clause.
Empty fibres have no points or irreducible components to test. A zero-dimensional
nonempty fibre fails purity. The node equation remains literally uv in every
characteristic. Pointwise locality imposes no purity assumption.

Searches: the initial msearch LeanFinder query on nodal algebraic-space étale
locality returned generic smooth/étale results; Loogle for IsNodalRelativeCurve and
HasNodalCurveCharts returned zero with an unknown-identifier message; Mathlib grep
Nodal|nodal in AlgebraicGeometry returned zero. Local rg found the candidate
ring-only IsNodalRelativeCurve, IsGeometricOrdinaryDoublePoint and universal-chart
HasNodalCurveCharts; none states these equivalences or the full scalar-compatible
scheme predicate. New-node searches are recorded verbatim in its mathlib_searches
and described below. No mathematical statement dispute is asserted.

## Repair of H2

1. Replaced the delivered stmt_dep lem-trf-nodal-point-etale-locality with the landed
   def-trf-completed-local-scalar-map, and added its bracket citation.
2. Replaced the delivered stmt_dep lem-trf-nodal-family-etale-source-locality with
   same-delivery def-sfb-scheme-nodal-relative-curve. The first attachment attempt
   failed because deliver2's generated module-format probe cannot import the legacy
   source-locality module. Used the return's explicit alternative: a full
   scalar-compatible definition in its own module without IsNodalRelativeCurve.
   Moved IsOrdinaryNodeOver and IsNodalRelativeCurveWithScalars there, listing both
   under the definition node's lean.declarations. Consumer theorem signatures stay
   exact; source-locality remains a proof import only.
3. Added stmt_dep and bracket citation def-a1-space-open-subspace for OpenSubspace.
4. Added stmt_dep and bracket citation def-weil-finite-type-morphism for the
   pointwise LocallyOfFiniteType hypothesis.
5. Rebuilt the item from current main; preserved proof, proof_deps, source, status
   and provenance. Compared retained packet versus current node: before repair
   only lean and stmt_deps differed. The wrapper rebases the concrete packet on
   current main; this is a changed ownership/interface packet, not an unchanged push.

## New nodes

`def-sfb-scheme-nodal-relative-curve` owns the full scalar-compatible scheme predicate
and ordinary-node helper in Sheaf.AlgebraicGeometry.SchemeNodalRelativeCurve. It
matches the direct Flat/LFP/geometric pure dimension one/nonsmooth closed-node
clauses above, with actual canonical completed scalars. Both definitions have
explicit data and no sorry. Source: curves.tex 0C59/0C5A/0C57. No new theorem or
postponed proof obligation is introduced.

Before adding it, searched the DAG for IsNodalRelativeCurve and nodal-family
predicates: the legacy ring-only helper is only listed in the source-locality
statement node, without a definition owner. Blueprint search "nodal relative curve"
returned zero matches, and ancestor returned None; preserved the inherited via
chain. LeanSearch query "flat locally finitely presented scheme morphism with pure
one dimensional nodal geometric fibres" returned eight generic flat/smooth/LFP
hits. LeanFinder query "nodal relative curve flat locally finite presentation pure
dimension one geometric fibres ordinary nodes" returned eight smooth/étale hits.
Mathlib grep IsNodalRelativeCurve|NodalRelative|nodal family in AlgebraicGeometry
returned zero. Local rg in WeilConjectures and Sheaf found only the ring-only helper
and its source-locality theorem. The new definition is the precise scalar-compatible
interface authorized by the return, reusing the completed-scalar map owner. The node
records actual search outputs, same_as = [], and the item's inherited ancestor.

## Statement corrected

statement_change.old_statement stores the current main's original text verbatim.
Added the missing definition citations, clarified the completed-scalar convention,
and spelled out the locally finite type chart scope already present in proof step 5
and in the accepted Lean. This follows Stacks 0DSG(4)--(7), 0DSF and curves 0C57.
The recorded old_stmt_deps is the current main list. The proof and proof_deps are
unchanged. No blueprint unit statement is changed.

Complete citer audit (all stmt_deps and proof_deps in dag/nodes):

- lem-sfb-nodal-point-blowup-local-descent: holds:true. Its chartwise nodal descent
  and completion comparison use the same criteria on locally finite type fibre
  charts. Definition ownership and explicit scope do not change this use.
- lem-sfb-space-nodal-locus-base-change: holds:true. Its largest-open construction
  uses the same source-open chart criteria and base change, and its geometric-point
  description uses the same locally finite type completion comparison.

Neither citer is edited. No dependency node requires a lean-only repair.

Validation after the repair: scompile.py compiled both modules separately against
published live sources, cleanly and within 60 seconds (definition module 38.7 s,
consumer library 9.5 s). The definition module contains no sorry. Both recorded
signatures were checked verbatim against the files; autoImplicit and
relaxedAutoImplicit are disabled, and all lines are at most 100 characters.
The revised deliver2.py --no-push passed server preflight and compilation
(commit 434a093bd21); its staged set is precisely the two modules, two nodes,
and this report. The earlier attachment-only import failure is repaired by the
full scalar-compatible definition module, not suppressed or worked around.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
