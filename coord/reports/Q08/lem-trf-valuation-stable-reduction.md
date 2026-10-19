## Worker report

Stage 2 of `lem-trf-valuation-stable-reduction`, repairing the return on immutable
head `38ae52fe0855`. The sole delivered Lean module is
`Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction`, which states
`AlgebraicGeometry.MultipointedCurve.exists_stableEtaModification_of_isSepClosed`.
The theorem has `sorry` as its entire proof. Its docstring retains all seven proof
steps of the current DAG node. The mathematical statement and proof plan are unchanged.

The retained packet was first submitted to `deliver2.py --no-push`; it passed at
`a2102cc67c`. That mechanical pass did not resolve the independent review's duplicate
names, so this repair removes their definitions rather than merely renaming them.
The current shared item still has no Lean record; its earlier Q93 review was stage 1.
Comparison of the saved item with the current shared node found only `lean` and
`stmt_deps` different. The delivery wrapper rebases the repaired packet on current
`newtargets-dag`; no direct Git operation or shared-file edit was made.

Hypothesis and clause correspondence:

- A separably closed field K is `(K : Type u) [Field K] [IsSepClosed K]`.
- `(V : ValuationSubring K)` is a specified subring of K with the element-or-inverse
  property. Mathlib supplies `IsFractionRing V K`; its canonical inclusion is
  `V.subtype`. No discreteness or Noetherian hypothesis is imposed.
- Finite height is `[Finite (PrimeSpectrum V)]`: prime ideals of a valuation ring
  are totally ordered, so this is exactly a finite chain, including height zero.
- The base is `Spec (.of V)`, and `C : MultipointedCurve (Spec (.of V))` is the
  existing structure from `Sheaf.TraceFormula.MultipointedCurve`. Its fields
  `X`, `D`, `x`, `d`, `i`, `comm` are the two schemes, their structure maps, the
  marking, and the equality `d = i ≫ x`.
- Flatness is `flat_X` and `flat_D`. Global finite presentation is respectively
  `lfp_X`, `qc_X`, `qs_X` and `lfp_D`, `qc_D`, `qs_D`, retaining all three clauses
  of the dependency's convention. `closed` is `IsClosedImmersion i`.
- Pure relative dimensions one and zero are `pure_X` and `pure_D` on the
  scheme-theoretic fibres. They use the existing `Scheme.IsPureDimension`, defined
  using `topologicalKrullDim` on each irreducible component. No properness,
  separatedness, connectedness or nonemptiness is required of the curve.
- The generic-point map is `Spec.map (CommRingCat.ofHom V.subtype)` from Spec K.
  `hsmooth` is `Smooth` of the curve's base-change projection `pullback.snd C.x`.
  `hmarking` is `Etale` of `pullback.snd C.d` along the same map.
- The conclusion gives `C'` over the same Spec V and `f : Hom C' C`. The existing
  `Hom` has curve and marking maps, their two equations over the base, and the
  equation commuting with the marking. It introduces no extension of V or K.
- `f.IsStable` is the existing full stable-eta-modification predicate from
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`. Its first clause is
  `f.IsEtaModification`: both maps are proper; each is an isomorphism over an open
  whose source and target are schematically dense; both canonical base changes to
  Spec K are isomorphisms. The base-change maps are constructed by `pullback.map`.
- Schematic density is injectivity of the open immersion's `app W` for every open
  W, exactly injectivity on sections of the map O_Z -> j_* O_U. Source density is
  also present, as in an isomorphism between schematically dense opens.
- Its next clause is `C'.IsSemistable`. Every point in the algebraic-closure
  geometric fibre is in `smoothLocus` or satisfies `Orgogozo.IsOrdinaryDoublePoint`;
  the marking structure map is etale and every marking point lies in the relative
  smooth locus. The ordinary-double-point predicate uses the maximal-ideal adic
  completion and the scalar-compatible nodal ring of two-variable power series.
- Stability's final clause excludes a contracted projective-line component having
  at most two special points. The existing `IsStable` quantifies over closed
  embeddings of the existing `ProjectiveLine` over the algebraic closure of the
  base residue field, with image an irreducible component. It uses the actual
  canonical fibre map `f.curveBaseChange`. A component meeting `specialPoints` in
  cardinality at most two must have non-subsingleton image. This is the node's
  exclusion, including infinite sets of special points.
- `specialPoints` is the union of the range of the canonical base-changed marking
  and the nonsmooth locus of that geometric fibre. It uses the source marking,
  not the full inverse image of the target marking.

Dependency declarations read and used:

- `Sheaf.TraceFormula.MultipointedCurve`:
  `AlgebraicGeometry.MultipointedCurve` (`def-trf-multipointed-curve`).
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `AlgebraicGeometry.MultipointedCurve.Hom`, its `curveBaseChange` and
  `markingBaseChange`, `MultipointedCurve.markingBaseChange`, `IsSemistable`,
  `Hom.IsEtaModification`, `specialPoints`, and `Hom.IsStable`
  (`def-trf-multipointed-curve-modification`). The public import gives all of them.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`; the dependency also records
  `IsSepClosure`, which is not needed for this theorem's assumption.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring`, `subtype`
  and its fraction-ring instance.
- The existing pair and modification modules use `Spec`, `Spec.map`, `Flat`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`,
  `IsClosedImmersion`, `Smooth`, `Etale`, `IsProper`, the scheme fibre and pullback
  constructions, and `Scheme.IsPureDimension`.
- Their geometric nodes reuse `Sheaf.Paper.OrgogozoInductionData`:
  `Orgogozo.geometricPoint`, `IsOrdinaryDoublePoint`, `nodeRing`, `localScalar`;
  the original Mathlib `AdicCompletion` and `MvPowerSeries`; and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveLine`.
- The now-recorded proof dependency
  `Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction` is imported
  without `public`; its theorem
  `AlgebraicGeometry.Temkin.valuation_semistable_stable_contraction` uses the
  very same `MultipointedCurve`, `Hom`, `IsEtaModification`, and `IsStable`.
  The other six non-Mathlib proof dependencies have no recorded Lean module.
  Mathlib scheme gluing and proper permanence are included as proof imports.

Edge cases rechecked: the empty curve and empty marking are admitted by the existing
structure; fibre dimension predicates on empty fibres are vacuous. Empty marking on a
nonempty curve leaves stability's singular-point test intact. Rank zero, nondiscrete
positive finite rank, non-Noetherian valuation rings, arbitrary characteristic,
separably closed imperfect fields, disconnected curves and nonseparated/nonproper
curves are included. Contracted lines with zero, one or two special points are
excluded; those with at least three or infinitely many are allowed. Noncontracted
lines have no additional condition. Universes are explicit and `autoImplicit` is false.

Searches retained from the saved packet (`searches.jsonl` records the actual results):

- msearch.py leanfinder: stable reduction over finite-height separably closed
  valuation fields for multipointed curves; hits concerned Weierstrass reduction
  and valuative criteria, not this existence theorem.
- msearch.py leansearch: flat finitely presented curves with flat zero-dimensional
  marking, and stable marked modifications; hits concerned the constituent
  flat/smooth/etale notions. msearch.py loogle, `semistable`: no hits.
- msearch.py grep, `multipointed|semistable|stableModification|SchematicallyDense`
  in Mathlib/AlgebraicGeometry: no hits. The saved direct upstream search and
  blueprint_refs searches found no exact theorem.
- Repair searches: direct rg in the current shared `lean/Sheaf` and `dag/nodes`
  found the two existing definition nodes listed above. Their complete source
  declarations and docstrings were read. A repeat direct rg in upstream
  `WeilConjectures` for `MultipointedCurve`, the item id and the theorem name
  found no match. The definitions are reused through their recorded modules.

No statement correction or disputed statement is made. The original statement and
seven-step proof stay verbatim. `stmt_deps` gains only the two landed definition
nodes. No new definition node or dependency repair remains in this delivery.

## Repair of the returned delivery

The return lists four duplicate declarations in
`Sheaf.AlgebraicGeometry.Curve.MultipointedStableModification`:
`AlgebraicGeometry.MultipointedCurve`, `MultipointedCurve.Hom`,
`MultipointedCurve.Hom.IsEtaModification`, and `MultipointedCurve.IsSemistable`.
All four are now imported from their existing owning modules. The entire copied
module and its proposed `def-trf-multipointed-stable-modification` node have been
removed from the packet, along with the unchanged saved copy of
`def-trf-multipointed-curve`. No replacement alias or renamed duplicate remains.
The theorem now uses the existing `C.x`, `C.d`, and `f.IsStable` interfaces.

## Second reading by Q08

This is a separate self-check, not a claim of an independent second agent's review;
the task explicitly prohibits starting other agents. I reread the item and both
existing definition modules against the revised theorem. The fields `x` and `d`
render the original maps; `comm` provides their compatibility; `IsStable` contains
all three conclusion clauses. Its contrapositive cardinality formulation excludes
exactly the contracted components in the node. The original seven-step docstring
is retained. The four duplicates identified by the maintainer are absent because
this packet now declares only the existence theorem. All node fields other than
`lean` and the permitted additions to `stmt_deps` match the current shared node.

Validation: `scompile.py Q08 lem-trf-valuation-stable-reduction` on the sole delivered
file succeeded. It also compiled the recorded contraction proof-dependency overlay;
the sandbox and library checks were clean. Final delivery uses the prescribed
`deliver2.py --no-push` preflight and compilation, followed by `deliver2.py`.
