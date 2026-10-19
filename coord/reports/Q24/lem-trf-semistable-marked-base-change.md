## Worker report

The delivery states all parts of lem-trf-semistable-marked-base-change in seven named
theorems, each with `sorry`, and adds the missing semistable-pair and geometric-stability interface. The landed
`AlgebraicGeometry.MultipointedCurve` is reused without changing its node or module. No proof
is attempted. The item's natural-language statement and proof are unchanged.

Source checks retained from the saved packet: the worker opened Temkin's Stable Modification of Relative Curves, arXiv 0707.3953v3,
§1.2, page 2 (https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf), and Stacks
0C5B (https://stacks.math.columbia.edu/tag/0C5B). Temkin defines multipointed curves using
flat finite-presentation maps, permits empty marking and nonseparated/nonproper curves,
and defines exceptional components by distinct intersection points with the marking and
singular locus. The definition module follows these conventions. The existing
Orgogozo.IsSemistableGeometricCurve additionally requires connectedness and reducedness;
it is not used to impose these extra hypotheses. Only its existing ordinary-double-point
predicate and canonical chosen geometric point are reused.

Clause-by-clause rendering (namespace AlgebraicGeometry.MultipointedPair):

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| Arbitrary scheme T, arbitrary base-change T' → T | `{T T' : Scheme.{u}}`, `(g : T' ⟶ T)`; no finiteness, separation, properness, Noetherian or characteristic conditions on the bases. |
| Two schemes over T and a marking over T | `MultipointedPair.curve`, `.marking : Over T`, `.inclusion : marking ⟶ curve`. The Over morphism supplies the structural commutation. |
| Curve and marking flat | `IsMultipointed P := ∃ C : MultipointedCurve T, ofCurve C = P`; the existing `C.flat_X` and `C.flat_D` fields impose these on the exact structural maps. |
| Both structural maps finitely presented | Existing fields `C.lfp_X`, `C.qc_X`, `C.qs_X` and `C.lfp_D`, `C.qc_D`, `C.qs_D`, transported by the exact underlying-pair equality, impose `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`. |
| Pure relative dimensions 1 and 0 | Existing `C.pure_X` and `C.pure_D` fields give `∀ t, (C.x.fiber t).IsPureDimension 1` and the marking version with 0, transported by `ofCurve C = P`. This includes empty fibres. |
| Marking closed | The existing `C.closed : IsClosedImmersion C.i`, transported by `ofCurve C = P`. |
| Canonical base-change pair | `P.baseChange g`, using `(Over.pullback g).obj` on both schemes and `.map` on the marking. No arbitrary replacement maps or choices. |
| Multipointedness preserved without semistability | `isMultipointed_baseChange`, hypothesis `hP : P.IsMultipointed`, conclusion `(P.baseChange g).IsMultipointed`. |
| Integral generic-base conditions | `generic_smooth_etale_baseChange`: `[IsIntegral T]`, `[IsIntegral T']`, generic points `η,η'` with `IsGenericPoint _ Set.univ`, and `hg : g η' = η`. |
| Generic curve smooth, marking etale | `hC : Smooth (P.curve.hom.fiberToSpecResidueField η)`, `hD : Etale (P.marking.hom.fiberToSpecResidueField η)`. Conclusion states both properties on the base-changed fibres over η'. `hP` retains the multipointed-curve assumption. |
| Semistable source, all structural conditions retained | `IsSemistable` includes `P.IsMultipointed`; `isSemistable_baseChange` assumes exactly `P.IsSemistable` and concludes it after g. |
| Chosen geometric fibres | `Orgogozo.geometricPoint T t` is exactly `Spec (AlgebraicClosure (T.residueField t)) → T`; `.baseChange` gives the specified pullback. It does not silently replace these by all larger algebraically closed field-valued points. |
| Only ordinary nodes at nonsmooth points | In `IsSemistable`, for each t and each fibre point x, non-formal-smoothness of its stalk map implies `Orgogozo.IsOrdinaryDoublePoint` of that fibre morphism at x. This is a scalar-compatible ring equivalence from the maximal-ideal `AdicCompletion` of the stalk to `MvPowerSeries (Fin 2) Ω / (X₀ X₁)`; existing `Orgogozo.localScalar` specifies the coefficients. |
| Etale marking and its smooth location | `Etale P.marking.hom` and `∀ d, (P.curve.hom.stalkMap (P.inclusion.left d)).hom.FormallySmooth`. Under the included local finite presentation, the latter is membership in Mathlib's `Scheme.Hom.smoothLocus`, whose defining set is exactly this predicate. |
| Relative smooth locus pulls back | `smoothLocus_baseChange` equates the set of points with formally smooth stalk map upstairs to the inverse image of the corresponding set downstairs under `pullback.fst P.curve.hom g`. |
| These properties local for open covers | `isMultipointed_isSemistable_iff_openCover` gives both iff assertions. `(I : Type w)`, `(U : I → T.Opens)` and `hU : ∀ t, ∃ i, t ∈ U i` describe arbitrary covers, including an empty cover of an empty base. Restrictions are the same canonical base changes along `(U i).ι`. |
| Compatible pair morphism with semistable source and multipointed target | The stability theorems have `hP : P.IsSemistable`, `hQ : Q.IsMultipointed`, over-T maps f and d and `hcompat : P.inclusion ≫ f = d ≫ Q.inclusion`. |
| Fibrewise irreducible components isomorphic to P¹ over the scalar field | `HasGeometricStability` quantifies a closed immersion j from `ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t))))`; its range must belong to `irreducibleComponents`, and its composite with the structure map must equal the canonical projective-line structure map. On the reduced nodal fibre this represents exactly the reduced component scheme being P¹, not just a topological rationality predicate. |
| Component contracted by f | `(Set.range (j ≫ ((Over.pullback (Orgogozo.geometricPoint T t)).map f).left)).Subsingleton`. Its image is nonempty since P¹ over a field is nonempty, so this is contraction to exactly one point. |
| No contracted P¹ with at most two special points | The consequent is `2 < Set.encard` of the set of x in the component range and either the geometric marking range or the nonsmooth locus. This counts distinct points in the fibre, not branches of the normalization. Infinite sets also satisfy this bound, so no finiteness assumption is smuggled into the definition. |
| Geometric stability preserved by arbitrary base change | `geometricStability_baseChange`, using the canonical `(Over.pullback g).map f`. |
| Geometric stability local on the base | `geometricStability_iff_openCover`, with the same arbitrary cover and restrictions. |
| No preservation assertion for modifications | None of the seven conclusions asserts properness, schematic density, or an η-modification. |

Every variable and universe is explicit (`autoImplicit false`); the field and scheme universes
coincide as in the existing geometric-fibre API, with no smaller independent test-field universe.
The cover universe w is arbitrary. All definition data are explicit. The only postponed
proofs are the seven named theorems belonging to this item, each with source and proof plan
in its docstring; the first contains the complete fourteen-step DAG proof.

Dependency declarations inspected and reused:

- `def-trf-multipointed-curve`: `Sheaf.TraceFormula.MultipointedCurve` / `AlgebraicGeometry.MultipointedCurve`; all fields and its docstring were read for this repair. `ofCurve` uses `C.x`, `C.d`, `C.i`, `C.comm`; `IsMultipointed` reuses the complete bundled structure.
- `def-trf-semistable-multipointed-pair`: `Sheaf.AlgebraicGeometry.SemistableMultipointedPair` / `AlgebraicGeometry.MultipointedPair` and its five accompanying definitions, supplied here.

- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension` / `topologicalKrullDim`.
- `def-nagata-projective-space-base-change`: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` / `AlgebraicGeometry.ProjectiveSpace`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` / `CategoryTheory.Limits.pullback`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties` / `AlgebraicGeometry.IsIntegral`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` / `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth` / `AlgebraicGeometry.Smooth`.
- `def-sc-generic-point`: `Mathlib/Topology/Sober.lean` / `IsGenericPoint`.
- `def-sc-p1-standard`: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits` / `AlgebraicGeometry.ProjectiveLine.TwistData`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale` / `AlgebraicGeometry.Etale`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat` / `AlgebraicGeometry.Flat`.
- `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` / `CategoryTheory.Limits.pullback`.
- `def-weil-irreducible-components`: `Mathlib/Topology/Irreducible.lean` / `irreducibleComponents`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic` / `AdicCompletion`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic` / `MvPowerSeries`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension` / `AlgebraicGeometry.Scheme.IsPureDimension`.
- `def-trf-orgogozo-induction-data`: `Sheaf.Paper.OrgogozoInductionData` / `AlgebraicGeometry.Orgogozo.UniversalTruncatedComparison`.

The geometricPoint, nodeRing, localScalar and IsOrdinaryDoublePoint definitions were read
in full in Sheaf.Paper.OrgogozoInductionData. The pure-dimension definition was read in
Sheaf.AlgebraicGeometry.PureDimension. The ProjectiveLine abbreviation is the existing
ProjectiveSpace with ULift (Fin 2) homogeneous coordinates, not a second projective line.
The TwistData declaration of def-sc-p1-standard is not needed as statement data; its
TransitionUnits module is retained as a proof dependency. All already-stated proof-dependency
modules are imported without `public`, while statement interfaces are public imports.
Unstated proof dependencies remain future stage-3 work, not hypotheses of these statements.

Edge cases checked: empty D; empty X; empty fibres; empty T and its empty open cover;
arbitrary nonproper and nonseparated X; any characteristic including 2; reducible and
irreducible nodal fibres; a self-nodal component (the singular point is counted once);
contracted and uncontracted P¹ components; 0, 1, 2 and 3 special points; larger special-point
sets. A rational nodal component that is not isomorphic to P¹ is not incorrectly counted as
an exceptional P¹. The generic assertion has nonempty integral bases, as the node requires.
No node fault or statement dispute was found.

Searches made for this repair: msearch.py LeanSearch queried “semistability and geometric
stability of a marked relative curve with canonical pullback pair”: eight generic permanence
hits, no exact match. LeanFinder queried “semistable multipointed pair ordinary nodes etale
marking and no contracted projective line with at most two special points”: eight generic
smooth/etale and elliptic-curve hits, no match. Mathlib grep queried
`Semistable|Multipointed|GeometricStability` under AlgebraicGeometry: zero hits. The new node
records the returned search records verbatim. Local rg in the DAG, upstream WeilConjectures
and lean/Sheaf found the landed `MultipointedCurve` and Orgogozo definitions, which are
reused; no marked relative semistability or geometric-stability declaration exists there.
`tools/blueprint_refs.py search 'semistable multipointed'` returned zero blueprint nodes.
The original packet's broader searches remain in searches.jsonl and scratch/.

## New nodes

`def-trf-semistable-multipointed-pair` supplies the raw pair, canonical base change,
forgetful `ofCurve`, the predicate of being exactly the underlying pair of the existing
multipointed curve, and the semistability and geometric-stability predicates. Its source is
Temkin §1.2 and Stacks 0C56. The LeanSearch, LeanFinder, Mathlib grep, local project/upstream
and DAG searches above are recorded in mathlib_searches. This node supplies the remaining
notions and does not replace `def-trf-multipointed-curve`. The generic pair type has no
geometric property fields, allowing the locality iff and permanence conclusions to be stated
before supplying their proofs. `ofCurve` has explicit data and the supplied commutation proof.
`IsMultipointed` is a proposition, not a choice of data: equality fixes the two schemes and
all three morphisms exactly. Thus it imposes precisely the existing structure's properties.
All six declarations carry this new node's source/blueprint docstrings. The item cites this
new node, the landed multipointed-curve node and the landed Orgogozo node.

## Returned delivery repair

The return on immutable head `330e7fe7be84` observed that another delivery had already
created `def-trf-multipointed-curve`. The required initial dry run of the retained packet
confirmed that the saved copy would now overwrite a landed dependency record and reported
missing lean.note and Dependency modules. I read the landed node and its full source
`Sheaf.TraceFormula.MultipointedCurve`. Its interface is usable and is now imported and
reused, so no dependency repair is needed. The sandbox copy of that node was removed, and
the duplicate geometric definition was removed from the delivery. The retained helper module
was renamed to SemistableMultipointedPair, assigned to the new definition node above, and
its `IsMultipointed` predicate now refers to the landed structure through exact underlying-pair
equality. The seven theorem signatures and the item's natural-language statement and proof
remain unchanged. The new node is the only replacement for the former new-node packet;
the landed node is not delivered or altered.

## Validation

`scompile.py Q24 lem-trf-semistable-marked-base-change` compiled both delivered modules
separately in dependency order through its private overlay. Every stage returned exit code 0
with no compiler warning or error. The final dry run and delivery recheck the same packet.
The wrapper adds the direct-delivery independent-review notice; no second reader is claimed.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
