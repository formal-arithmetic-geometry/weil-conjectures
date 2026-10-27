## Worker report

This delivery states `AlgebraicGeometry.AlgebraicSpace.space_derived_hom_mayer_vietoris`
in `Sheaf.AlgebraicGeometry.SpaceDerivedHomMayerVietoris`. Its sole postponed proof is
this theorem. All helper definitions contain actual constructions; the two structures
package precisely specified comparison and long-exact-sequence data whose existence is
asserted by the theorem. They supply neither arbitrary boundaries nor arbitrary
replacement pullback functors. Every helper is listed in `lean.declarations`.

Sources read: `literature/stacks-project/spaces-perfect.tex`, lemma-mayer-vietoris-hom
(Tag 08H9), and the complete proof and statement of lemma-exact-sequence-lower-shriek
(Tag 08GV). The module docstring gives the source; the theorem docstring carries all
eight accepted DAG proof steps, including their supporting nodes and the normalized
cone calculation for arbitrary pullback. The statement and accepted proof split are
unchanged. The additional statement dependencies are already landed interfaces actually
used by the statement, as authorized by brief-stage2 §5. There are no new nodes or
dependency repairs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Size convention: explicit `universe u w`, `S : Scheme.{u}`, the recorded
  `X.SmallModules` model, and `HasDerivedCategory.{w}` on each participating space.
  The localization morphism universe `w` is independent of the scheme universe. No
  equality between site-object, site-morphism, coefficient or localization universes
  is added. The small-model equivalence is the recorded actual affine-chart restriction.
- Base scheme and algebraic spaces: `{S : Scheme.{u}}` and `X U V T : AlgebraicSpace S`.
  The original small étale ringed topos is `X.Modules`; the derived category is the
  already recorded equivalent-small-model `X.DerivedModules`.
- Open inclusion: `hOpen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
  jU.hom.hom` is the defining property of `OpenSubspace`, expressed for a presentation
  by an algebraic space over X. It is not an assumed arbitrary open subset of points.
- Representable étale map: `hV : IsEtale jV.hom.hom`, using precisely the recorded
  scheme-test definition of representable étaleness.
- Reduced closed complement: `C : ClosedSubspace X`, `hC : IsReduced ...`, and
  `hSupport : pointImage C.val.arrow.hom.hom = (pointImage jU.hom.hom)ᶜ`.
  This uses the recorded closed subfunctor, reducedness and point-class topology.
- Isomorphism over that complement: `hIso : IsIso (Limits.pullback.snd jV.hom
  C.val.arrow.hom)`. This is the sheaf fibre product over X, projected to C.
- Overlap: arrows `a : T ⟶ U`, `b : T ⟶ V`, and `sq : IsPullback a b jU jV`.
  A presented pullback includes every choice of fibre-product object; no existence
  assumption beyond the named overlap is introduced. `a ≫ jU` is its structure map.
- Arbitrary E,F and all integral Ext degrees: every occurrence is quantified over
  `E F : X.DerivedModules` and `n : ℤ`, with Ext written literally as
  `E ⟶ F⟦n⟧` or the corresponding restricted objects. The pair of local groups is
  the binary product, canonically the direct sum for abelian groups.
- Exact étale restrictions: all use the existing `spaceDerivedPullback` functors.
  The already landed `spaceEtaleDerivedRestriction_existsUnique` identifies these
  with exact termwise restriction. The helpers use that same normalized restriction,
  without replacing it by a new functor.
- First middle map: `(spaceExtPullback jU M.sU n f,
  spaceExtPullback jV M.sV n f)`.
- Second middle map: `spaceExtRestrictionOver jU a ... p.1 -
  spaceExtRestrictionOver jV b ... p.2`, where each summand uses the fixed
  `spaceDerivedPullbackComp` and the equality of composite structure arrows.
- Full long exactness: `SpaceHomLES` asserts `Function.Exact` for restriction then
  difference, difference then boundary, and boundary then next restriction, for
  every integer n. Replacing n by n-1 gives the incoming overlap term in the node.
  It also asserts additivity of each boundary map; boundary zero follows by applying
  its additive equation at zero and cancellation in the Hom abelian group.
- Specified boundary: `SpaceHomMayerVietorisData.delta` is constrained by
  `SpaceHomDeltaNormalized` on EVERY original-site complex. The predicate includes
  existence of the chain zero-composite and short-exactness proofs, and equates the
  boundary with `DerivedCategory.triangleOfSESδ` of the actual signed sequence after
  applying `smallModuleComplex X`. Thus no vacuous implication can conceal failure
  of short exactness. The first and second chain maps are induced by the recorded
  `elementaryEtaleSumDifferential` and `elementaryEtaleSumEvaluation`.
- Applying derived Hom into F: `spaceHomConnecting` applies the inverse of the
  overlap adjunction's `homEquiv`, shifts the transposed arrow by one, precomposes
  with delta, and uses `shiftFunctorAdd` to identify F[n][1] with F[n+1].
- Normalization of that adjunction and comparison: `SpaceEtaleHomAdjunction` has
  the fixed right adjoint `spaceDerivedPullback j`. `ordinarySections` imposes the
  recorded multiplication formula on every tensor section. Its `transpose` field
  identifies EVERY original chain-Hom transpose with the termwise original
  `etaleModuleShriekAdjunction`; `factors_normalized` uses the resulting restriction
  and shriek comparisons. This rules out twisting the lift summands by a counit-
  preserving automorphism. `evaluation` retains the actual evaluation counit.
- Contravariance in E: the second conjunct of `SpaceHomLES` says
  `boundary E' F n (restriction.map x ≫ f) = x ≫ boundary E F n f`.
- Covariance in F: its third conjunct says
  `boundary E F' n (f ≫ (restriction.map y)⟦n⟧') =
  boundary E F n f ≫ y⟦n+1⟧'`.
  The middle maps are actual restriction/composition functions, so their two
  variances are already specified by these functors and canonical natural isos.
- Every base-change map h: the main theorem quantifies over arbitrary `h : X' ⟶ X`,
  arbitrary pullback presentations `sqU sqV sqT`, and compatibility of the overlap
  projections. No flatness assumption is imposed on h or its component maps.
- The new square is elementary: the conclusion supplies its open-immersion property,
  `hV'`, a reduced closed `C'` with precisely complementary support, and the required
  complement pullback isomorphism. It does not assert that the pullback of C is reduced.
- All canonical Ext pullback maps and composition identifications:
  `spaceExtPullback` maps the given arrow by the existing Lh*, then uses its shift
  comparison. `spaceExtSquarePullback` conjugates the local map by the recorded
  `spaceHomPullbackSquare`, constructed here from
  `spaceDerivedPullbackComp` and the square equation. `SpacePullbackShiftNormalized` requires the
  existing total-derived counit to commute with shifts and the canonical shifts
  on termwise pullback and localization; shifts are not arbitrary extra assumptions.
- Morphism of the entire long exact sequences: `SpaceHomBaseChange` has the two
  equations for restriction (one for U and one for V), the equation for the signed
  difference, and the equation for boundary, all for every E,F,n. The theorem supplies
  the new `SpaceHomMayerVietorisData` and normalized shifts as conclusions.
- No boundedness, quasi-coherence, flatness, quasi-compactness or separation
  hypotheses occur. In particular the node covers unbounded complexes and
  non-quasi-compact, non-separated representable étale V.

Dependency declarations read (statement constructions use definition interfaces;
chart-calculus results below are proof-only):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsRepresentableWith`, `Modules`, `pullback`, `isEtale_comp`, `structureSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent specialization of Mathlib `SheafOfModules` and its morphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and the existing shifts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleTensorPullback`, `moduleTensorSection` and `ModuleChart`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`, with `ClosedSubspace`, `IsReduced` inherited.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace` and the recorded `Point` classes.
- `Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact`:
  `elementary_etale_shriek_exact`, `EtaleModuleSumExact`, `etaleModuleSum`,
  `etaleModuleSumCounit`, `elementaryEtaleSumDifferential`,
  `elementaryEtaleSumEvaluation`, `etaleModuleShriekAdjunction`.
  This recent module was read with `scompile.py --source` from the live server.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`,
  `spaceDerivedPullbackCounit`, `spaceDerivedPullbackComp`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`: `smallModuleComplex`,
  `smallModuleRestriction_additive`, `moduleOriginalPullbackCounit`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`, `spaceEtaleDerivedRestrictionFactors`,
  `spaceEtaleDerivedRestriction_existsUnique`, `spaceHomPullbackSquare`, constructed here from
  `spaceDerivedPullbackComp` and the square equation.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`:
  `triangleOfSESδ`, `triangleOfSES` and `triangleOfSES_distinguished`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`.

Proof-only imports follow every currently stated proof dependency: KFlatIndependentCoefficients,
KFlatResolutionIndependentCoefficients, TensorClosed, Localization.Adjunction,
KFlatHomotopyTriangulated, DerivedCategory.ExactFunctor, Localization.Predicate,
ModuleSheavesColimitsForgetful, RingedTopoiDerivedPullbackIndependent and
HomotopyCategory.Adjunction. The proof nodes `lem-sfb-space-etale-sum-pullback` and
`lem-sfb-ringed-kflat-pullback-ses-triangle` currently have no recorded Lean module and
are therefore not imported; this theorem does not use them in its statement.

Edge cases checked before writing and again on rereading:

- X empty, U empty and U=X. The hypotheses are the actual complement condition;
  no nonemptiness or proper-open constraint is present. For U empty, V is forced
  to be an isomorphism over the whole reduced complement, as in the source.
- T empty and E=0 or F=0: Hom groups and the canonical SES boundary reduce to zero;
  the quantifiers and constructors still apply.
- n=0 and negative n: literal integral shift is used, not nonnegative Ext of
  objects of the heart. The incoming degree n-1 term is retained.
- h=id and an arbitrary nonflat h: all pullbacks remain the same recorded derived
  functor with its normalized compositors. No equality of reduced complements
  before/after arbitrary base change is assumed.
- Infinite étale fibres and non-quasi-compact V: the imported shriek is the genuine
  sheafification of lift-indexed finite-support direct sums; no finite-fibre model
  is substituted. Binary direct sum of the two displayed Hom groups adds no
  finiteness constraint on these fibres.
- Arbitrary localization universe w: all participating derived categories are
  explicit. There is no universal typeclass quantification over ALL algebraic spaces.

Searches performed via prescribed `msearch.py Q45 <item>` and read-only rg:

- leanfinder: `Mayer Vietoris long exact derived Hom algebraic spaces elementary
  distinguished square` -> 8 hits, site MayerVietorisSquare and ordinary abelian-
  sheaf SES; none has unbounded derived Hom and arbitrary derived pullback boundaries.
- loogle: `CategoryTheory.ShortComplex, DerivedCategory, Function.Exact` -> 0 hits.
- grep: `mayer.vietoris|MayerVietoris` in `CategoryTheory` -> 10 hits, primarily
  `Sites/MayerVietorisSquare` and `Sites/SheafCohomology/MayerVietoris`; wrong terms.
- leansearch: `Mayer Vietoris exact sequence derived Hom of algebraic spaces
  elementary distinguished square` -> 8 hits, the same sheaf-cohomology construction
  and topological-open squares, no exact match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for MayerVietoris, derived Hom and
  algebraic-space operations: the scheme/topological `derived_hom_mayer_vietoris`
  applies to two opens of a RingedSpace and only states two exactness positions in
  degree zero; it does not state this algebraic-space elementary-square theorem.
- Search for the item id in `lean/WeilConjectures` -> no declaration.
- Search for `space_derived_hom_mayer_vietoris|SpaceHomMayerVietoris|SpaceHomLES|
  spaceExtPullback` in both library roots -> no existing declaration.
- Direct reads of Mathlib `DerivedCategory/ShortExact`, `DerivedCategory/ExactFunctor`
  and the existing module operations supplied the constructors used here.

No statement fault or STATEMENT-DISPUTED issue was found. The added auxiliary records
express comparisons needed to state this same node, and are not a second definition
of the underlying categories, restriction functors, extension functors or derived pullback.

Validation: prescribed `scompile.py` compiled the file separately both as a sandbox
module and at its final module path, with no errors or non-sorry warnings (39.2 s and
37.8 s respectively in the original delivery's final pre-delivery run). No local Lean invocation, global
build, direct shared-repository edit or git command was used.

## Second reading by Q45

I reread the node, source statements, full dependency signatures and final module after
writing it. This is a separate self-review pass, not a claim that another agent reviewed
it: the dispatcher explicitly forbids starting agents; the maintainer independently
reviews this delivery.

The checks matched the geometric binders, actual complement isomorphism, pullback
presentations, all three exactness positions for every integer degree, original signed
counits, canonical SES boundary formula, both variance equations and all four base-change
equations against the node. The size convention is represented by participating small
models and arbitrary common w. No forbidden geometric or boundedness assumption appears.

One meaningful mismatch found during this pass was that preservation of an evaluation
counit alone does not uniquely normalize the extension comparison: a permutation of lift
summands could preserve evaluation. I added `ordinarySections`, the all-chain-map
`transpose` equation, and `factors_normalized`, using the recorded ordinary tensor section
formula and literal original extension/restriction adjunction. The final boundary uses
these fixed comparisons. Another check ensured short-exactness in the boundary
normalization is existentially supplied, rather than the antecedent of an implication
that might be vacuous. Compiler checks repaired explicit type parameters and the chart
source in the section formula. Every definition has real data, and the only theorem
proof is the expected whole-proof `sorry` of this item. No statement correction is needed.

## Repair of returned delivery

The independent review of immutable head `c10fe3c96e35` returned H2: the two added
statement dependencies `lem-sfb-space-derived-etale-chart-calculus` and
`lem-trf-space-etale-module-pushforward-restriction` supplied only plain helper
definitions, not theorem conclusions. Removed both from `stmt_deps`, retaining the
three definition interfaces for derived modules, derived pullback and base-change
comparisons. The original node statement and proof fields remain unchanged.

As requested, the item module now owns two documented helpers:
`spaceHomPullbackSquare` is the inverse compositor, equality transport and compositor
for the commuting square, using `spaceDerivedPullbackComp` from the already cited
`def-sfb-space-derived-pullback`; `spaceHomChartEtaleHom` is the explicit constructor
`⟨q.hom⟩` into the site given by `etaleMap` from the already cited
`def-trf-algebraic-space`. Their data contains no postponed proof. The former replaces
both uses of `spaceDerivedChartPullbackSquare`; the latter replaces the section-formula
use of `moduleChartEtaleHom`. The chart-calculus module is a proof-only import
for its existing proof-dependency edge. Neither removed theorem supplies a statement
construction. Both new helpers are listed in `lean.declarations`.

Compared the sandbox node against current main without Git: only `lean` and the
previously added `stmt_deps` differ. The three definition dependencies remain; the two
returned theorem additions are removed. Rereading confirms that the theorem signature,
all geometric hypotheses, boundary normalization, both variances, and arbitrary-base-change
clauses retain the independently reviewed mathematics. No statement correction is needed.

Repair validation: the compile initially approached or exceeded the fixed 60-second
limit. A diagnostic run identified expensive zero-preservation instance search for
additive complex functors. Prioritizing Mathlib's existing
`Functor.preservesZeroMorphisms_of_additive` instance locally avoids that search; no
new instance, hypothesis, mathematical construction or theorem is introduced. All
temporary profiler options and progress checks were removed. The final theorem
signature still matches `lean.statement` verbatim, and the declaration list contains
exactly the module's 25 declarations, including the two new documented helpers.

Final repaired module: server confirmation by prescribed `scompile.py` succeeded in
45.3 seconds, under nice 19, two threads and the unchanged 60-second limit, with
no errors or non-sorry warnings.
