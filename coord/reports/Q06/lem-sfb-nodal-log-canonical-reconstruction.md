## Worker report

The module `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction` states
`AlgebraicGeometry.exists_nodal_log_canonical_reconstruction`, with one `sorry` and
its fourteen-step proof plan in the docstring. No theorem is proved. The two helper
constructions, `nodalLogFundamental` and `nodalLogPullbackSection`, have actual data.
The two named predicates spell out this item's naturality and affine reconstruction
clauses; they are not additional hypotheses or new independent notions.

The earlier O2 landing was stage 1: the merged report explicitly says no Lean was
written, and the node has no Lean record. It therefore does not supersede this
stage-2 assignment. No duplicate delivery of that proof split is being made.

Hypothesis-by-hypothesis correspondence:

- The base scheme and its local Noetherian hypothesis are `S : Scheme.{u}` and
  `[IsLocallyNoetherian S]`. Global Noetherianity is not imposed.
- The family and its marking use the already recorded `P : MultipointedCurve S`.
  Its fields `X`, `x`, `D`, `d`, `i` and `comm` give the curve, structure morphism,
  marking, its structure morphism and its inclusion over S. `flat_X`, `lfp_X`,
  `qc_X`, `qs_X` express flatness and finite presentation. `pure_X` records ordinary
  pure curve fibres, which follow from the stipulated geometric purity. The marking
  fields give flat finite presentation of the zero-dimensional closed marking,
  properties already forced by a finite disjoint union of sections. Thus this
  established representation imposes no extra mathematical restriction.
- Projectivity in the node's finite-projective-space convention is
  `[IsHProjective P.x]`, using the recorded upstream definition.
- The finite list of disjoint sections is `n : ℕ`, the isomorphism
  `marking : (∐ fun _ : Fin n ↦ S) ≅ P.D`, and `hmarking`, its over-S equation.
  Explicitly the ith section is `Sigma.ι _ i ≫ marking.hom ≫ P.i`; its section
  equation follows from `hmarking` and `P.comm`. Coproduct components are disjoint
  and `P.i` is a closed immersion. Conversely disjoint sections of this separated
  family give precisely this split closed marking. No nonempty index is required.
- Their images lie in the relative smooth locus by `hsmooth`.
- `hnodal : HasNodalGeometricFibres P.x` gives nonempty connected geometric fibres,
  dimension one, and the actual completed-local-ring nodal condition at every
  nonsmooth geometric point. It uses `AdicCompletion`, the maximal ideal of the
  stalk, and `MvPowerSeries (Fin 2) Ω` modulo `(X 0 * X 1)`.
- `hgeometric` explicitly retains reducedness and PURE dimension one on every
  geometric fibre. Total Krull dimension one alone is not used in place of purity.
  All field, algebraic-closedness and geometric-point binders are explicit.

Clause-by-clause correspondence:

- The conclusion supplies `D : MarkedNodalDualizingDegreesData P` using its existing
  interface, not the theorem `marked_nodal_dualizing_degrees` (whose integral-base,
  generic-smoothness and modification hypotheses are inapplicable here).
- `D.omega` is the relative line, and `D.dualizing : NodalDualizingDatum P.x D.omega`
  includes invertibility, the fundamental class, regular affine presentation coverage,
  the ordered Jacobian formula and the actual local sheaf Ext descriptions.
  `D.canonical` gives the unique fundamental-class-compatible isomorphism to any
  other such normalized datum. No line is chosen from uncharacterized existence.
- The first explicit conjunct is `IsIso` of the restriction of
  `D.dualizing.fundamental` to `P.x.smoothLocus`. The source is the restriction of
  relative differentials, canonically the differentials of that open over S.
- `D.base_change` quantifies over EVERY `T' : Scheme.{u}` and map `q : T' ⟶ S`.
  The line is the actual `tensorPullback (pullback.fst P.x q)` of `D.omega`.
  The displayed formula on `1 ⊗ da` fixes the fundamental class after base change.
  No local-Noetherian assumption is made on T'. It also states Cartier pullback
  and identifies the pulled-back log line with the base-changed marking twist.
- `D.cartier` states that the actual closed marking `P.i` is effective Cartier.
  Its kernel ideal is the sum divisor's ideal. `markedNodalLine P D.omega` is the
  previously defined `D.omega ⊗ₘ P.i.ker.toModulesᵛ`, exactly omega tensor O(D).
  `D.marked_invertible` retains invertibility of this line.
- `D.normalization_degree` states the component formula and finiteness of the
  special-point set. It tests every integral closed reduced component Z of every
  geometric fibre and uses its function-field normalization, the same summands as
  `Scheme.reducedNormalization`. Its properness premise follows from projectivity
  and the closed immersion, so it excludes no component in the node.
  `markedNodalComponentDegree` is the recorded Euler-characteristic degree of the
  pullback to `Z.normalization`; `markedNodalComponentGenus` is arithmetic genus
  there. `markedNodalBranches` is the inverse image of the union of markings and
  AMBIENT nonsmooth points. Its `ncard` counts distinct normalization points, so
  a self-node contributes TWO branches and an ordinary marking contributes one.
- The positivity antecedent explicitly uses `2*g - 2 + ncard` for every normalized
  geometric component. Its consequence is ampleness of the restricted actual log
  line above EVERY affine open V of S, using the recorded `Scheme.Modules.IsAmple`.
  Invertibility witnesses are bound explicitly, with no file-local instances.
- The reconstruction implication assumes just that same relative-ampleness condition.
  `A : RelativeSectionAlgebra P.x (markedNodalLine P D.omega)` supplies the ACTUAL
  homogeneous sections, scalar action, unit, tensor multiplication and restriction
  maps. This is the existing quasi-coherent affine-basis encoding of the sum of
  direct-image powers, not an arbitrary graded algebra or a degree-zero equality
  with O(S). `r : P.X ≅ A.data.relProj` is an isomorphism, not just cohomology or
  an open immersion; `A.IsCanonicalMap r.hom` fixes evaluation on trivializing
  charts using the existing `Proj.fromOfGlobalSections`.
- `NodalLogAffineReconstruction` states the affine R-scheme conclusion for every
  `S ≅ Spec R`. It uses precisely `sectionRingGrade` of the upstream
  `InvertibleSectionRing`. Its coefficient homomorphism is specified on EVERY
  element of R using the structural pullback into degree zero. The displayed
  over-Spec-R equation uses `Proj.toSpecZero` and this homomorphism. Nonvanishing
  preimages and the formula for every fraction a/s^n specify the canonical map,
  including n=0. The section-ring operations are the recorded tensor operations.
- `NodalLogReconstructionIsNatural` tests each over-S isomorphism of the curve and
  marking preserving their inclusion. The log-line comparison preserves the actual
  log fundamental class (fundamental class followed by the canonical divisor section).
  This pins the comparison on the schematically dense complement of nodes and
  markings. It asserts the EXISTENCE of the induced graded algebra isomorphism,
  specified in every degree on every base affine by actual pullback of sections,
  followed by the power of this line comparison. The final equation is the square
  with `GradedAlgebraData.relProjIsoOfIso`; no arbitrary Proj map is substituted.
  It applies to every normalized datum E and every canonical section-algebra map
  for the isomorphic marked family. No extra hypotheses on that family are needed.
- Neither conclusion assumes a smooth generic fibre, integral or normal S, a map
  to another curve, or genus at least two.

Dependency declarations used (the corresponding modules are explicit public imports):

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: the actual dual marking ideal
  and its invertibility; `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso`;
  `Sheaf.AlgebraicGeometry.NodalDualizingDatum`: `NodalDualizingDatum`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `Scheme.Modules.degree`, `Scheme.arithmeticGenus`;
  `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`
  and its integral components; `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization`, `Scheme.fromNormalization`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` and
  `nonvanishingLocus`; `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `GradedSheafAlgebra`; `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj`.
- `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`:
  `Scheme.Modules.InvertibleSectionRing`, `SectionRingComponent`, `sectionRingGrade`.
- `Sheaf.TraceFormula.MultipointedCurve`: `MultipointedCurve`;
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.markingBaseChange`;
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`;
  `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees`:
  `MarkedNodalDualizingDegreesData`, `markedNodalLine`,
  `markedNodalComponentDegree`, `markedNodalComponentGenus`, `markedNodalBranches`.
- `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`:
  `Scheme.Modules.RelativeSectionAlgebra`, its `IsCanonicalMap` and `evaluate`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`:
  `Scheme.GradedAlgebraData.relProjIsoOfIso`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSection` and `tensorPullbackSectionAdjunction`;
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackGenerator`.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  the existing generic `boundaryTensorPowIso` and `boundaryPullbackPowIso`.
  These generic constructions require no square-zero hypothesis. A temporary copy
  of the first construction was removed upon finding this existing declaration.

The definition dependencies now identify the declarations used by the statement:
`def-sfb-marked-nodal-dualizing-degree-data`,
`def-sfb-relative-section-algebra-canonical-map`,
`def-sfb-relative-proj-iso-of-graded-iso`, and
`def-sfb-tensor-power-pullback-comparisons`. Each binds existing real definitions in
an unchanged module. The statement uses none of the four replaced theorem nodes'
conclusions, and none of these definitions is chosen from those theorems. The other
statement dependencies and all proof dependencies are retained. Modules shared by
statement definitions and proof theorems remain public imports; imports used only
for the proof plan remain non-public.
`lem-sfb-lci-curve-fundamental-class` has no recorded Lean module yet and therefore
has no import; its step is retained verbatim in the natural-language proof plan.

Edge cases checked before finalizing:

- n=0: the coproduct marking is empty, its ideal is O(X), and the twist is trivial.
- Empty S and hence empty X: geometric conditions and component positivity are
  vacuous; the zero section ring has empty Proj, so reconstruction remains valid.
- Smooth unmarked genus zero and genus one give -2 and 0, respectively, so neither
  incorrectly triggers the positivity implication.
- A three-marked projective line has degree 1; a one-marked smooth genus-one curve
  has degree 1. An irreducible rational self-node contributes two distinct branches.
- Markings cannot coincide with nodes or with each other; both are recorded inputs.
- Nonreduced or nonnormal locally Noetherian bases are permitted. Arbitrary
  base change includes non-Noetherian bases, the identity and empty base changes.
- Degree-zero section algebra need not equal O(S). The affine structural map uses
  the specified coefficient map; no projective normality or generation in degree
  one is asserted. Fraction formulas include power zero and empty standard opens.
- All geometric field tests use the scheme universe u, as the recorded interfaces
  do. No independent smaller field universe or site universe equality is imposed.

Searches (executed with the prescribed msearch wrapper and direct source reads):

- LeanFinder: “A projective flat marked nodal curve has a canonical relative
  dualizing line whose marking twist has component degree 2g-2 plus special points,
  is relatively ample when positive, and reconstructs the curve as the Proj of its
  section algebra”. Eight results: Weierstrass-curve constructions and
  `AlgebraicGeometry.Proj.fromOfGlobalSections`; none is this statement.
- Loogle: `AlgebraicGeometry.NodalDualizingDatum,
  AlgebraicGeometry.Scheme.Modules.RelativeSectionAlgebra` returned the diagnostic
  “unknown identifier AlgebraicGeometry.NodalDualizingDatum”; this was not treated
  as an absence proof. The valid follow-up query `"Proj.toSpecZero"` returned
  exactly the existing structure map, which is used.
- Mathlib grep through msearch: `Nodal|nodal|logCanonical` in AlgebraicGeometry:
  no hits. Direct rg of the upstream and Sheaf sources for this blueprint id:
  no hits. Source searches by nodal/marked/section algebra located the reused
  interfaces above. Searching tensor-power isomorphisms found and reused
  `boundaryTensorPowIso`, rather than retaining a second definition.
- Opened the original node and each statement dependency's statement and binding;
  read the recorded declarations and docstrings in the local Lean/Mathlib source.
  Source readings: Moduli of Curves `lemma-gorenstein-dualizing` and `lemma-stable`;
  Varieties `lemma-ampleness-in-terms-of-degrees-components`; Morphisms
  `lemma-characterize-relatively-ample` and `lemma-proper-ample-is-proj`.
  The genus restriction of the unmarked 0E74 is not added to this marked statement.

No statement correction or STATEMENT-DISPUTED flag is needed. Compared with the
returned immutable head c76dcf08274c, the Lean module and its statement are unchanged.
The repair replaces four theorem statement dependencies by four definition owners
and documents those owners below. Compared with current live main, the item changes
only in `lean` and `stmt_deps`; all its original statement dependencies remain.
The delivered module compiles cleanly through scompile.py on the server; all names
and universes are explicitly bound and lines are at most 100 characters. The
expected theorem `sorry` is the only postponed proof.


## New nodes

All four new definition nodes use `existing: true`; no Lean definition is copied,
changed, or added. The declaration signatures are extracted verbatim from their
existing modules. They are in this item's chapter and unit and inherit its ancestor
(`blueprint_refs.py ancestor` returns `None`) and path, prefixed by this item.

- `def-sfb-marked-nodal-dualizing-degree-data` binds
  `AlgebraicGeometry.MarkedNodalDualizingDegreesData` and the four associated
  definitions `markedNodalLine`, `markedNodalComponentDegree`,
  `markedNodalComponentGenus`, and `markedNodalBranches`, in
  `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees`. Its definition records the
  data, uniqueness, arbitrary base change, Cartier twist and normalized-component
  degree fields exactly. The genus, degree and branch formulas have the same maps
  and normalization as the existing helpers. This replaces the inappropriate
  statement dependency `lem-trf-marked-nodal-dualizing-degrees`; its theorem has
  additional integral-base and generic hypotheses that this statement never uses.
- `def-sfb-relative-section-algebra-canonical-map` binds
  `AlgebraicGeometry.Scheme.Modules.RelativeSectionAlgebra`, its `evaluate`, and
  its `IsCanonicalMap` in
  `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`. The additive section
  equivalences, scalar, unit, product and restriction fields and every chart binder
  of `IsCanonicalMap` are described explicitly. The node cites the tensor comparison
  definition below. This replaces `lem-trf-scheme-ample-canonical-proj-criterion`
  in statement dependencies; that theorem's ampleness equivalence is not an input.
- `def-sfb-relative-proj-iso-of-graded-iso` binds
  `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjIsoOfIso` in
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`. Its direction is
  `B.relProj ≅ A.relProj` for `e : A ≅ B`, with the canonical fraction map and inverse.
  This replaces `prop-nagata-relative-proj-functoriality` in statement dependencies;
  the existing constructor, not the proposition's conclusions, supplies the map.
- `def-sfb-tensor-power-pullback-comparisons` binds
  `AlgebraicGeometry.Scheme.Modules.boundaryPullbackPowIso`,
  `boundaryTensorPowIso`, `boundaryPullbackTensorIso`, and
  `boundaryPullbackComparison` in
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`. Its
  recursion includes degree zero and the adjunction-normalized unit comparison.
  It applies to arbitrary module sheaves and morphisms. This replaces
  `lem-sc-square-zero-ideal-tensor-unit` in statement dependencies; its square-zero
  hypotheses and theorem are irrelevant to these generic constructions.

For each node, new LeanSearch and LeanFinder searches were run with its own
plain-language query, plus the prescribed Mathlib grep over the eight declaration
names. The exact recorded queries and returned hit names are in each node's
`mathlib_searches` and the wrapper's `searches.jsonl`. LeanSearch/LeanFinder returned
normalization, Weierstrass, ordinary Proj charts or general pullback/tensor-power
results, not these project definitions. The Mathlib grep returned zero hits.
Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` found exactly the reused
interfaces. DAG searches of these names found attachments in the four theorem
nodes, but no definition node; the last two tensor-power constructions had no
attachment. `blueprint_refs.py search` for `marked nodal`, `section algebra`,
`relative Proj isomorphism`, and `tensor product pullback` returned no matches.
The separately landed `markedNodalSpecialPoints` has a different interface (a
single curve with an indexed marking and a canonical component); the current
family interface uses arbitrary geometric base change and integral component
inclusions, and is preserved as the return requests. No new Lean counterpart is
introduced for either interface.

Sources were reopened at Stacks 0E6R and the component argument of 0E74, 01VJ(5),
and 01CD. The preexisting declarations' full signatures and docstrings were read,
including the complete fields of the two structures. No source assertion is
replaced by a weaker result, and no existence theorem is used to select data.

## Second reading by Q06

This is the worker's repair self-check; the maintainer's independent reading is
still required. The original mathematics was accepted clause by clause in the
return. I reread the saved node and the unchanged Lean file: local Noetherianity
is `[IsLocallyNoetherian S]`; the flat finitely presented marked family is
`P : MultipointedCurve S` with projectivity `[IsHProjective P.x]`; the splitting
by `Fin n` and `hmarking` records disjoint sections also for `n = 0`; `hsmooth`,
`hnodal` and `hgeometric` retain the smooth marking, nodal and reduced pure
geometric-fibre hypotheses. The conclusion's datum retains the canonical
normalized dualizing line, arbitrary base change and degree `2g-2+r` fields.
The displayed `IsIso` is the smooth-locus normalization. The positivity implication
concludes ampleness above every affine base open. The second implication uses
exactly this relative ampleness to obtain an isomorphism with relative Proj,
`IsCanonicalMap`, the full affine section-ring form, and the naturality square.
All clause mappings and edge cases in the Worker report still apply unchanged.

The ownership check found and repaired exactly the returned H2 point: none of
`MarkedNodalDualizingDegreesData`, `RelativeSectionAlgebra`, `IsCanonicalMap`,
`relProjIsoOfIso`, `boundaryTensorPowIso` or `boundaryPullbackPowIso` is a choice
of the four theorem statements. All four theorem nodes are now absent from
`stmt_deps`; each used definition has a cited definition owner. The theorem nodes
and their existing modules are untouched. The item retains its original
`statement`, `proof`, and `proof_deps`. No statement correction is needed.
The initial saved-packet dry run passed at 5b1fc09d252, but did not by itself
establish this ownership condition; the substantive repair is the four node
records and this dependency replacement. The standalone scompile.py invocation
compiled both sandbox and library contexts cleanly (3.4 s and 4.1 s).


## Repair of returned head ff692ae461a4

The retained packet repairs both dependency errors in the 2026-10-22 return.
`def-sfb-relative-section-algebra-canonical-map` now cites the delivered
`def-sfb-tensor-power-pullback-comparisons` for its canonical power comparison.
`def-sfb-tensor-power-pullback-comparisons` instead cites the existing owners
`def-weil-sheaf-of-modules-category`, `def-pur-sheaf-tensor-product`, and
`def-pc-module-pullback`; its statement explicitly gives the recursion and unit
normalization implemented by the unchanged published definitions.
Neither node refers to the nonexistent `def-sc-tensor-pullback-power-comparison`.

The saved-packet dry run passed at 8cddc2018ee against the refreshed live base.
The repair self-check verified that every statement dependency of all five packet
nodes resolves on that base or in this packet, and that each new definition's
bracketed citations equal its statement dependencies. Compared with current main,
the item changes only in `lean` and `stmt_deps`; its mathematical statement,
proof plan, and proof dependencies are retained. The signature matches the Lean
file verbatim, its variables and universe are explicit, all lines fit 100 columns,
and its only postponed proof is the item's theorem. No Lean changes were needed.
