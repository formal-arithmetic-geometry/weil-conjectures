## What changed

`integralMatrix_analytic_cover` has a complete Lean proof of its original signature. It chooses a constant-rank cover, detects zero matrices from their continuous entries, uses a finite ultrametric maximum argument near every nonzero matrix fiber, restricts the inequalities to open neighborhoods, and composes their covers. All finite ranks, including zero rows/columns, and empty cover members are covered by the same proof.

The original three data definitions and IsMonHom instance move verbatim to `IntegralMatrixAnalyticData`, publicly reexported by the original module, so the lower proof modules avoid a cycle. The new regular pullback comparison, pulled-back coefficient function and sectionwise continuous direct-image map have explicit constructions and proved APIs. Their irreducible wrappers keep elaboration from expanding the entire module pullback and basis comparison; the defining equation is explicitly unfolded where needed. Existing signatures and definitions are unchanged. The change record is `coord/changes/C1-integral-matrix-analytic-data.md`.

The analytic maximum lemma, regular-coefficient and matrix-entry pullback compatibility, rank-zero matrix detection, faithful coefficient detection and zero-neighborhood theorem are proved. Every delivery module compiles cleanly through lcompile.py, and deliver3.py --no-push has passed. The three unchanged direct consumers IntegralMatrixEntryProperties, IntegralMatrixPivotCover and IntegralRegularRationalUnit were also checked against the sandbox overlay; the remaining geometric work is isolated in the two public statements below.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_analytic_cover` (one of one original sorries).

New proved statements: `ContinuousMap.exists_open_dominating_member`, `AlgebraicGeometry.ProEtale.CondensedRing.integralRegularCoefficient_pullback`, `AlgebraicGeometry.ProEtale.CondensedRing.integralMatrixFunctions_pullback`, and `AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_zero_neighborhood`. All their private helpers are proved, and all definitions are constructed without sorry.

Added holes, both strictly parts of the original argument:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_pointwise_rank`, node `lem-weil-pbc-integral-matrix-pointwise-rank`, in `IntegralMatrixPointwiseRank.lean`. It still needs construction of geometric evaluation for these actual integral/rational internal module categories, compatibility with coefficient scalar extension and the continuous realization, and the finite-free cokernel dimension calculation. Its conclusion is only pointwise rank equality; it has no pivot, norm, nonvanishing or cover-assembly conclusion.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousChart_scheme_naturality`, node `lem-weil-pbc-continuous-chart-scheme-naturality`, in `ContinuousChartSchemeNaturality.lean`. It still needs the canonical chart's scheme naturality square. A compiled exploratory proof reduces the square by adjunction and unit-composition coherence to equality of explicit maps on relative profinite test objects. The pullback-pasting projection identity and the continuous-section formula on an arbitrary object over Spec Z were also proved in local experiments. The remaining issue is combining these with the canonical profinite-test chart formula: the elaborated proof repeatedly exceeds the kernel heartbeat limit while checking definitional conversions involving concrete pullback objects. The final delivered chart statement is left whole, with its complete proof in words; no conversion timeout is hidden in a delivered proof. It has no matrix, rank, module endomorphism or cokernel hypothesis and no covering conclusion. The induced evaluation-at-unit identity and regular-coefficient compatibility are proved in `IntegralRegularCoefficientPullback.lean`.

This is a decomposition: one upper hole closed and two geometric holes added, not an unconditional proof or a net reduction in holes. No arbitrary witness is chosen from an unproved existence statement in any definition.

## No longer needed

The original module's direct public imports `Sheaf.Paper.ContinuousCoefficientRealizations` and `Mathlib.Data.Matrix.Basic` are replaced by their public reexport through `Sheaf.Paper.IntegralMatrixAnalyticData`; both dependencies remain used. Its former proof imports `Sheaf.Paper.ContinuousIntegralCoefficients` and `Sheaf.Paper.GeometricFieldProEtaleEvaluation` also leave this module: integral coefficients remain publicly available through the data module, and geometric evaluation is imported privately by `IntegralMatrixPointwiseRank`, where that planned proof needs it. Thus all three old proof-dependency nodes (`def-weil-pbc-continuous-integral-coefficients`, `lem-weil-pbc-continuous-coefficient-realizations`, `lem-weil-pbc-geometric-field-proetale-evaluation`) are retained transitively; none is globally pruned. The geometric-field module's existing evaluation theorem still needs its bridge from sheaves of modules to these internal module categories and the integral scalar-extension compatibility.

In the new finite-family lemma, `Mathlib.Analysis.Normed.Group.Ultra` is a private proof import; only `Mathlib.Topology.MetricSpace.Ultra.Basic` needs public visibility for the ultrametric hypothesis. No module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement was found, and the unit route is retained. The original node's continuous maximum and geometric-rank steps were prose rather than Lean glue. The maximum is now proved directly, and the exact geometric-rank and scheme-naturality obligations are explicit. The source attribution remains qualified: Bhatt--Scholze Section 6.8 supplies the continuous integral framework and kernel-closure application; this particular matrix pivot argument is an agent reduction, not a matrix proof written in Lemma 6.8.7.

The existing coordinate definition expands several monoidal and biproduct comparisons. Leaving that large term exposed in dependent cover elaboration caused slow definitional equality. An explicit irreducible wrapper for the new pulled-back coefficient function, together with an abstract cover-assembly helper, makes the actual proof compile in seconds without changing the existing data or the time limit.

## New nodes

`def-weil-pbc-integral-matrix-analytic-data` records the explicit normalized coefficient constructions and the unchanged relocated data. See `coord/changes/C1-integral-matrix-analytic-data.md`.

`lem-weil-pbc-finite-continuous-ultrametric-pivot` records the proved finite-family local maximum argument.

`lem-weil-pbc-continuous-chart-scheme-naturality` records the remaining geometric chart square.

`lem-weil-pbc-integral-regular-coefficient-pullback` records the proved scalar coefficient identity.

`lem-weil-pbc-integral-matrix-functions-pullback` records the proved biproduct-entry reduction to the scalar identity.

`lem-weil-pbc-integral-matrix-pointwise-rank` records the remaining rational-cokernel geometric rank calculation.

`lem-weil-pbc-integral-matrix-zero-neighborhood` records the proved conversion from constant rank and one zero fiber to a zero open neighborhood.

## Second reading by C1

1. **Interfaces: pass.** I compared the sandbox with the shared repository using `diff` and the declaration parser. The entire signature of `integralMatrix_analytic_cover`, including its original rational-cokernel hypothesis, normalized pullback, canonical chart and pointwise norm conclusion, is byte-identical. The three relocated definitions and the anonymous `IsMonHom` instance have byte-identical signatures and bodies. The relocation and new explicit helpers are declared in `coord/changes/C1-integral-matrix-analytic-data.md`. I ran `downstream.py --uses` for each moved name: their external users are precisely IntegralMatrixEntryProperties, IntegralMatrixPivotCover and IntegralRegularRationalUnit; they retain the same data and public visibility through the reexport. No target or definition used by a target changes its meaning.

2. **Kernel and data: pass, conditional on the two listed holes.** I read all eight modules and compiled the delivered set in import order with `lcompile.py`; no errors or warnings occurred. The only remaining `sorry` tokens are the complete public theorems `integralMatrix_pointwise_rank` and `continuousChart_scheme_naturality`. Every definition is constructed explicitly; inverses come from specified isomorphisms, and no definition chooses an arbitrary object from an unproved existence claim. A scratch file prints the axioms of all 18 named public declarations: the data and finite maximum lemma use only `propext`, `Classical.choice` and `Quot.sound`; the remaining dependent proofs additionally use `sorryAx`. The required delivery probe also checks private helpers. There is no forbidden declaration or kernel-check bypass.

3. **Split statements: pass as a decomposition.** The rank statement fixes the matrix and the original local-freeness premise and asserts only equality of its field ranks on each cover member. At a geometric point, right-exact scalar extension and inverse image, exact final-object evaluation, and the free cokernel presentation give rank `t-q`; the missing bridges between the actual module categories remain inside this one named obligation. Its conclusion has no pivot, inequality or neighborhood assembly. The chart statement has only a topological ring and scheme morphism and states equality of two explicit maps, without a matrix or local-freeness premise. Applying the coefficient adjunction and the pullback-pasting identity gives its stated proof. I checked the zero source/target, empty scheme and zero ring cases, and the identity scheme map; none requires an extra hypothesis. Both holes have their own nodes and full proof descriptions. New LeanFinder queries about adjoint realization under scheme pullback and free-cokernel point evaluation found only general adjunction, ordinary sheaf-module and stalk-rank APIs; Loogle found the standard adjunction naturality and matrix-rank lemmas. Repository searches found no duplicate for either obligation. The upstream adic-sheaf rank lemmas concern a different category. Neither hole can be closed by a direct use of these results in a few minutes.

4. **Route and pruning: pass after import repair.** The target genuinely combines zero-neighborhood detection, a finite ultrametric maximum, restriction of entries and binding of open covers. I checked the maximum proof: a nonzero member supplies a positive maximum, a finite intersection is open, and the ultrametric identity preserves the selected norm. Empty row or column types force the zero case. Zero rank is converted to a zero matrix, and faithful regular coefficients plus biproduct extensionality recover the zero morphism. The unit's `realized` statement and all three steps in `dag/units/sk-thm-properbasechange.json` remain intact; this change is below that route. I corrected `## No longer needed` to account for every old direct dependency. I restored the rank module's private geometric-evaluation import to match its open proof plan and made the ultrametric norm API private, with the hypothesis's defining module public. There is no global module pruning.

5. **DAG: pass after metadata repair.** I checked every new node against its module, source, creation record, chapter, unit and blueprint ancestry. Each `proof_deps` is the union of the proof steps' `uses`; the cover, coefficient and zero-neighborhood nodes describe the actual Lean reduction. I replaced the flattened `lean.statement` strings with the verbatim source signatures in all eight records. The original node's mathematical statement and the unit realization records are unchanged. The two holes are counted separately from the conditional proofs: one original hole closed, two added, net minus one hole closed, not an unconditional proof.

Second-reading changes: corrected the two import issues, recorded every removed direct import, and made the DAG signatures verbatim. No theorem statement or data construction was changed.
