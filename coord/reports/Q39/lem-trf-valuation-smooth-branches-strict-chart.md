## Worker report

The module `Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart` states
`AlgebraicGeometry.exists_valuation_smooth_branches_strict_chart`, with exactly one
`sorry`, its whole proof. No definition or auxiliary theorem is introduced.
The natural-language node statement and proof are unchanged. Its statement dependencies gain
three already landed definition nodes: `def-trf-multipointed-curve`,
`def-trf-multipointed-curve-modification`, and `def-trf-strict-semistable-curve`.
These provide the existing multipointed curve, semistability, and standard nodal algebra.
No dependency node is changed and no new node is required.

Read the item's full statement, source and seven proof steps, all original statement
nodes and recorded declarations, the three reused definition nodes and their modules,
and the recorded proof-module interfaces. No repair note for this item exists.
Temkin §1.2 and §4.3 (printed pp. 2 and 27), and Remark 4.5.2 (printed p. 33), were
opened at https://arxiv.org/pdf/0707.3953v3. Section 4.3 defines the two pair models;
its smooth-component observation is over a separably closed field. The node explicitly
labels the relative all-fibres result as an agent reconstruction; this delivery does
not attribute that stronger relative assertion to the paper. The docstring retains
all seven DAG proof steps, including ordering, vertical-ideal detection, fpqc descent,
the rescaling Jacobian calculation, and source-etale descent.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation subring V of K, fraction field K | `(V : ValuationSubring K)`; its defining `mem_or_inv_mem'` is the valuation alternative, and its subtype is the canonical map to its fraction field K |
| Prime ideals form a finite chain | `[Finite (PrimeSpectrum V)]`; comparability is inherent to a valuation ring, so this says the whole chain is finite |
| S and generic eta | `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.subtype)` |
| Flat finitely presented curve with pure dimension-one fibres | `P : MultipointedCurve (Spec (.of V))`: fields `flat_X`, `lfp_X`, `qc_X`, `qs_X`, `pure_X` |
| Closed marking, finitely presented and pure relative dimension zero | Fields `closed`, `lfp_D`, `qc_D`, `qs_D`, `pure_D`, with `comm` recording compatibility over S |
| Semistable geometric fibres | `hsemistable : P.IsSemistable`; on the algebraic-closure pullback each point is in the relative smooth locus or satisfies `Orgogozo.IsOrdinaryDoublePoint` |
| Completed local node with its scalar field | That existing ordinary-double-point predicate uses `AdicCompletion` at the maximal ideal and `Orgogozo.nodeRing Ω = MvPowerSeries (Fin 2) Ω / (uv)`, with explicit scalar compatibility |
| Etale marking lying in the relative smooth locus | The second and third clauses of `P.IsSemistable` are `Etale P.d` and `∀ e, P.i e ∈ P.x.smoothLocus` |
| Smooth generic curve | `hgeneric : Smooth (pullback.snd P.x (Spec.map (CommRingCat.ofHom V.subtype)))` |
| Reduced induced structure of every fibre component | `hcomponents` quantifies over every `s` and closed `Z` with underlying set in `irreducibleComponents (P.x.fiber s)`; it uses `(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι` |
| Each component smooth over the residue field at all its points | `Smooth ((vanishingIdeal Z).subschemeι ≫ P.x.fiberToSpecResidueField s)` |
| Every point x, affine Zariski source and base neighbourhoods | `∀ x`, existential `U : P.X.Opens`, `B : (Spec (.of V)).Opens`, `IsAffineOpen U`, `hB : IsAffineOpen B`, `x ∈ U`, `P.x x ∈ B` |
| Structure map factors through the base open | `U ≤ P.x ⁻¹ᵁ B`; the chart equations use the canonical `hB.fromSpec` from `Spec Γ(Spec (.of V), B)` |
| Affine-line model | `Spec (.of (Polynomial Γ(Spec (.of V), B)))`; its structural map is `Spec.map (CommRingCat.ofHom Polynomial.C)` |
| Compatible etale pair maps | `Etale h`, `Etale m`, both base equations, and `m ≫ Spec.map (ofHom (Polynomial.evalRingHom 0)) = pullback.snd P.i U.ι ≫ h` |
| Marked point, marking is exactly the inverse image of zero | The implication `x ∈ Set.range P.i → IsPullback m (pullback.snd P.i U.ι) zero h` |
| Smooth unmarked point, affine-line chart with empty source marking | In the smooth disjunct, `x ∉ Set.range P.i → IsEmpty (pullback (C := Scheme) P.i U.ι)` |
| Nonsmooth point, nodal model | The second disjunct is guarded by `x ∉ P.x.smoothLocus`; it supplies `c : Γ(Spec (.of V), B)` and an etale map to `(StrictSemistableModel.nodal c).scheme` |
| Equation uv=c and standard map over the base open | The existing nodal model unfolds to `Spec A[u,v]/(uv-c)`; `h ≫ ...baseMap ≫ hB.fromSpec = U.ι ≫ P.x` |
| Empty marking in the nodal model | `IsEmpty (pullback (C := Scheme) P.i U.ι)`. An empty source and empty standard marking have a unique compatible map, automatically an isomorphism and hence etale |

The smooth/nonsmooth disjunction chooses the models exactly as required by the final
point-specific assertions. At a marked point, semistability implies membership in the
smooth locus, so the first disjunct applies and its cartesian marking condition is active.
At a nonsmooth point the first disjunct is impossible, forcing the second. At a smooth
unmarked point the second is impossible and the first has empty marking. The base ring
is the coordinate ring of the affine open, a canonical presentation of the arbitrary A
in the node. Both maps of pairs are over this base: `hB.fromSpec` is a monomorphism,
so the displayed equations over S also give the equations over its affine open.

Dependency declarations used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the node also records `IsSepClosure`,
  whose signature and docstring were read; no separable-closure construction is needed).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, through the existing
  `Scheme.IsPureDimension` used by `MultipointedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, with `QuasiCompact` and `QuasiSeparated`
  for full finite presentation in `MultipointedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, and the published `smoothLocus`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, the
  existing marking's property field.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, through `MultipointedCurve`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, for actual
  scheme geometric fibres and marking restrictions, rather than sets of geometric lifts.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, through the existing
  nodal-completion predicate; `IsAdicComplete` is not needed.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, through `Orgogozo.nodeRing`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; the zero-section map is the spectrum
  of `Polynomial.evalRingHom 0`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, which identifies the existing
  `vanishingIdeal Z` subscheme as the canonical reduced induced closed subscheme.
- `Sheaf.TraceFormula.MultipointedCurve`: `MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`: `MultipointedCurve.IsSemistable`.
- `Sheaf.TraceFormula.StrictSemistableCurve`: `StrictSemistableModel.nodal`, `.scheme`,
  `.baseMap`, and their existing `strictNodalRing` construction.

Public imports expose the statement's notions; nonpublic imports are the recorded,
already stated proof dependencies. The four proof-only nodes without a Lean record
(`lem-trf-etale-descent-through-source-cover`, `lem-trf-ordered-nodal-branch-overlap`,
`lem-trf-space-chartwise-etale-permanence`,
`lem-trf-vertical-principal-ideal-fibre-detection`) are retained in the proof docstring
and DAG proof dependencies and do not need unstated imports. No statement depends on an
unavailable object. Mathlib leaves use the module carrying their recorded match.

Edge cases checked: empty D activates the smooth-unmarked and empty-marking clauses;
empty X makes the conclusion vacuous, consistent with existing pure-dimension conventions.
Empty fibres cause no component obligation. A field viewed as its own valuation subring
is included. No rank-one, discrete, Noetherian, excellent, separated, proper, connected,
geometrically irreducible or characteristic hypothesis is imposed. The component test is
for every base point, including generic and intermediate points, not only the closed fibre.
The nodal parameter is allowed to be any c in A, exactly as in the node; no unit or
nonzero restriction was added to the conclusion. Universe u is explicit everywhere.

Searches actually run with `msearch.py Q39 lem-trf-valuation-smooth-branches-strict-chart`:

- `leanfinder`: “Nodal curve over a separably closed finite height valuation ring smooth
  fibre components Zariski local strict semistable pair charts”: eight hits, including
  Weierstrass good reduction/minimality and standard smooth charts, none the relative
  marked nodal strict-chart theorem.
- `loogle`: `"semistable"`: zero hits.
- `grep`: `semistable|nodal`, subdirectory `AlgebraicGeometry`: zero hits.
- `leansearch`: “Every semistable marked curve over a finite height valuation ring with
  separably closed fraction field and smooth reduced fibre components has Zariski local
  etale affine line or nodal pair charts”: eight hits about schemes, standard etale pairs,
  Weierstrass good reduction and smoothness, none exact.
- `rg` in upstream `WeilConjectures/` and project `lean/Sheaf/`: semistability, multipointed
  curves, strict charts and the node id. Upstream has no target declaration. The project
  has the three reused definition modules; no theorem stating this node was found.
- `rg` in `dag/lean_names_upstream.json` for the item, proposed declaration, and nodal
  algebra name found no recorded duplicate. Read the returned smooth-chart signatures
  and the actual reused definitions rather than inferring a match from names.

The first compiler run found category inference choosing `Type` for a bare `pullback`
inside `IsEmpty`. The marking pullbacks now explicitly use `(C := Scheme)`.
Compilation and delivery verification are recorded below after the final checks.
No node fault or statement correction was required.

## Second reading by Q39

This is the worker's final self-check, not an independent-agent review: the dispatch
brief prohibits starting agents and assigns independent review to the maintainer.
With the node and module open, checked each clause in the table above, in particular
full finite presentation without separatedness, all fibres in `hcomponents`, scalar
compatibility of the geometric node, affine source and base opens, the direction of
the zero-section map and cartesian marking square, and forced chart choices at the
three kinds of points. The one implementation defect found was the category inference
in an `IsEmpty` pullback; the explicit scheme category fixes it without altering any
mathematical clause. No new definition or dependency replacement needs review.

Final validation: prescribed `scompile.py Q39
lem-trf-valuation-smooth-branches-strict-chart
lean/Sheaf/TraceFormula/ValuationSmoothBranchesStrictChart.lean` exited 0.
Both sandbox and library-path compilations were clean, with no errors or warnings.
The default per-invocation 60-second limit was retained; reported sandbox elapsed time
includes slot acquisition. No global build or direct Lean invocation was used.

Delivery dry run: `deliver2.py Q39 lem-trf-valuation-smooth-branches-strict-chart --no-push`
printed `OK (dry run): commit 9454ebd41c passes the preflight and compiles; nothing pushed`.
