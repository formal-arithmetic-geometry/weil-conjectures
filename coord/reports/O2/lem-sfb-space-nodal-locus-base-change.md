## Worker report

Repair of the returned delivery at immutable head affc2dabb5d1. Stage 2 only:
`Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange` contains four real predicate
helpers and the theorem `AlgebraicGeometry.AlgebraicSpace.exists_nodal_open_baseChange`
with its single `sorry`. The theorem retains all eight natural-language proof steps.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraic spaces over a scheme and size convention: `{S : Scheme.{u}}`,
  `(X Y : AlgebraicSpace S)`, `(f : X ⟶ Y)`. All test schemes and fields use `u`.
- Flatness: `hflat : OnEtaleCharts (fun _ _ h ↦ Flat h) f.hom.hom`.
- Local finite presentation: `hfp` with `LocallyOfFinitePresentation`.
  `OnEtaleCharts` quantifies over every pair of scheme charts, their representable
  étaleness, a scheme morphism, and the commuting-square equation. No atlas is an
  extra hypothesis.
- Existence of an open subspace: `∃ A : OpenSubspace X`, the recorded subtype of
  subfunctors with representable open-immersion inclusion.
- Nodal of relative dimension one: `HasNodalCurveCharts (A.val.ι ≫ f.hom.hom)`.
  This tests the scheme property on all étale diagrams, as Stacks 0DSG(6) states.
  `IsSchemeNodalCurve` includes flatness, local finite presentation, and the stated
  smooth-curve-or-node condition at every point of every geometric fibre.
- Largestness: every `B : OpenSubspace X` with that property satisfies `B ≤ A`.
- Every base change: arbitrary `(Y' : AlgebraicSpace S)` and `(g : Y' ⟶ Y)`.
  The actual pulled-back open is
  `A.val.preimage (Limits.pullback.fst f.hom.hom g.hom.hom)`.
  Its inclusion is representably open, its morphism to `Y'` has nodal curve charts,
  and every nodal open subfunctor `B` of the canonical presheaf pullback lies in it.
  Thus it is the largest nodal open after base change, precisely expressing
  commutation of the largest-open construction. The recorded fibre-product theorem
  ensures this canonical pullback represents the algebraic-space fibre product.
- Geometric fibres: for every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`, base map
  `s : Spec (.of Ω) ⟶ S`, and geometric map `g` to `Y`, take each étale scheme
  chart `a` of `Limits.pullback f.hom.hom g`. The structure map `b` to `Spec Ω`
  is tied to the canonical second projection by the displayed equation.
- Exact fibre subset: the image of `x` in `X` lies in `pointImage A.val.ι` iff
  `IsSmoothCurveOrOrdinaryNode b.left x`.
- Smooth curve points: `∃ W : C.Opens, x ∈ W ∧
  SmoothOfRelativeDimension 1 (W.ι ≫ b)`. This requires dimension one locally,
  including at nonclosed smooth points, without a purity assumption on all of `C`.
- Ordinary nodes: the other disjunct is explicitly
  `x ∈ closedPoints C ∧ IsGeometricOrdinaryDoublePoint Ω C x`, with
  `[IsAlgClosed Ω]`. The existing latter predicate is precisely a ring isomorphism
  from the maximal-ideal-adic completion of the stalk to `Ω[[u,v]]/(uv)`.
- The node's introductory properness/finite-type text sets terminology only; the
  actual lemma neither assumes properness nor concludes it. No such hypothesis is
  introduced. No global equidimensionality, connectedness or nonemptiness is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `AlgebraicSpace.IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its canonical projections.
- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`:
  `AlgebraicGeometry.IsGeometricOrdinaryDoublePoint`; its definition uses the
  recorded `AdicCompletion` and `MvPowerSeries (Fin 2)` definitions. Its unrelated
  projectivity/connectedness predicates are not used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`; its public
  dependency `AlgebraicSpacePointClasses` supplies `schemePointMap`.
- Proof imports: `AlgebraicSpaceEtaleOpenImage`,
  `AlgebraicSpaceFibreProductsEtaleCovers`, `Sheaf.TraceFormula.NodalOpenLocus`,
  `NodalCurveLCICriterion`, `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`,
  and the Mathlib flat/étale/finite-presentation/quasi-separated permanence APIs.
  The chart-locality and syntomic-fixed-dimension nodes have no recorded declarations;
  their roles remain in the proof docstring, and no substitute theorem is declared.

Edge cases checked: empty source, empty fibres, and empty base changes impose no
point conditions. For a disjoint union of a smooth surface and a nodal curve, the
smooth-relative-dimension-one condition excludes the surface. An isolated smooth
zero-dimensional point is excluded; a cusp fails the completed-node test. Ordinary
nodes are allowed in every characteristic. Disconnected fibres are allowed.
Completions are unchanged on open restrictions. The universal chart description
covers nonschematic fibres, and the base-change quantifier includes identities.
The universe of test fields is the scheme universe, so the test is not vacuous.

Searches retained from the original packet: LeanFinder's largest nodal locus query
returned only scheme flatness, openness and smooth-relative-dimension results;
Loogle's `AlgebraicGeometry.AlgebraicSpace, nodal` did not recognize the space name;
Mathlib grep `nodal|Nodal|AlgebraicSpace` had no match. LeanSearch's nodal-chart query
returned scheme smoothness/formal-unramifiedness results. Original direct searches
of the DAG, blueprint references, WeilConjectures and Sheaf found no nodal-space
predicate. The original query evidence is retained in sandbox `searches.jsonl`.

Repair searches rerun through msearch.py:

- LeanFinder: "largest nodal relative dimension one open locus of flat locally
  finitely presented algebraic space morphism commutes with base change" returned
  eight scheme flatness/openness/smooth-dimension hits, no matching theorem.
- Loogle: `AlgebraicGeometry.IsGeometricOrdinaryDoublePoint` returned zero hits
  with "unknown identifier"; this is not evidence against the project declaration,
  whose actual source and signature were read directly.
- Mathlib grep: `IsSmoothCurveOrOrdinaryNode|IsSchemeNodalCurve|OnEtaleCharts|
  HasNodalCurveCharts` in AlgebraicGeometry returned zero hits.
- Direct rg over WeilConjectures, Sheaf, and dag/lean_names_upstream.json for these
  four names, the main theorem name, and the item id returned no hits.
- Direct rg for `IsGeometricOrdinaryDoublePoint|IsOrdinaryNode|IsNodalRelativeCurve`
  found the ProjectiveNodalTower definition, the old theorem-module ordinary-node
  helper, and the inline scheme-family helper in NodalFamilyEtaleSourceLocality.

Sources reread: spaces-more-morphisms.tex, definition-nodal-family, 0DSG(6), and
0DSH; curves.tex, lemma-nodal-family, definition-nodal-family, and
lemma-locus-where-nodal. No statement correction or dispute is needed.

## Returned points repaired

1. A6/H12: removed `def-sfb-space-nodal-curve-charts.json` and
   `SpaceNodalCurveCharts.lean` from the packet. Inlined `IsSmoothCurveOrOrdinaryNode`,
   `IsSchemeNodalCurve`, `OnEtaleCharts`, and `HasNodalCurveCharts` into the item's
   module, with source/blueprint docstrings naming the item. `lean.declarations`
   lists those four and the theorem. The item's `stmt_deps` is exactly the live
   base list plus `def-a1-space-open-subspace`, `def-a1-space-point-topology`, and
   `def-trf-projective-nodal-tower`. There is no new unreachable DAG node.
2. F2: the node alternative is now the explicit closed-points conjunction with
   the existing `IsGeometricOrdinaryDoublePoint`, with `[IsAlgClosed Ω]` on the
   point predicate. The statement no longer uses the theorem-module helper
   `IsOrdinaryNode`. `NodalOpenLocus` remains a plain proof import.
3. Advisory considered: `IsNodalRelativeCurve` in the legacy non-module
   `NodalFamilyEtaleSourceLocality` expresses the equivalent scheme notion using
   pure dimension and a completion condition at nonsmooth points. The maintainer's
   requested four local helpers are retained here; no copy of that completion
   construction or separate definition node is introduced.

The prescribed initial saved-packet dry run passed at cce18eb749c. It still had the
explicitly returned node/module and ordinary-node interface, so that mechanical
pass was not treated as a repair. The Lean and JSON content has now changed as
requested; the packet is not an unchanged re-push.

## Second reading by O2

Repair self-check with the live node and the repaired module open; no separate
agent was started, as the dispatcher requires. Checked each clause against the
correspondence above. Both chart hypotheses quantify all étale diagrams, the
largestness clauses concern the actual inclusions, the base-change clause retains
largestness after every map, and the final iff tests every geometric-fibre chart.
The repaired ordinary-node alternative preserves both closedness and the exact
completed-local-ring condition. All five declarations are public and recorded,
all universes and variables are explicitly bound, and all four definitions have
real predicate bodies. Only the main theorem has `sorry`. No item statement,
proof, proof dependencies, source, status or other metadata was changed.

Validation: scompile.py compiled the single repaired file both as
`Sheaf.Stage2.Sandbox0` (8.9 s) and under its final library module name (10.7 s),
with no errors or warnings. The final deliver2.py dry run and delivery validate
this same one-module packet against the current live base.
