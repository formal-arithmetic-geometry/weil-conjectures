## Worker report

The module `lean/Sheaf/DeligneLaumon/Reduction/AffineHc2Pure.lean` states
`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine_geometricallyConnected`.
Its binders render the node's finite-field setting as a field `k₀` with `[Finite k₀]`, a prime
coefficient `l` with `[Fact l.Prime]` and `[Fact (ringChar k₀ ≠ l)]`, and an explicit embedding
`ι : PadicAlgCl l →+* ℂ`. The curve is `U₀ : Scheme.{u}` over `Spec (CommRingCat.of k₀)`;
`[IsAffine U₀]`, `[SmoothOfRelativeDimension 1 (U₀ ↘ Spec (CommRingCat.of k₀))]`, and
`[GeometricallyConnected (U₀ ↘ Spec (CommRingCat.of k₀))]` render smooth, geometrically
connected, affine curve. The lisse Weil sheaf is
`F : WeilSheaf k₀ l U₀` with `hF : F.IsLisse`, and the punctual purity hypothesis is
`hpure : F.IsPunctuallyPureOfWeight ι w`. The conclusion is
`(F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2)`, with the
`SmoothOfRelativeDimension.smooth` instance supplied in a `haveI` exactly as required by the
compact-support construction. The theorem proof is `sorry`, as required at stage 2.

The source statement is the blueprint node `lem-a1-affine-hc2-pure` in
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-affine-hc2-pure.md`.
Its proof dependencies are recorded in the node and the statement imports the upstream
interfaces used by them: `WeilConjectures.WeilSheaf.Cohomology` supplies
`WeilSheaf.compactlySupportedCohomology`; `WeilConjectures.DeligneLaumon.Reduction.Weights`
supplies `WeilSheaf.IsPunctuallyPureOfWeight`; and
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` (through the cohomology import) supplies
`FrobeniusModule.IsPureOfWeightOver`. The recorded dependency declarations are:
`FrobeniusModule.IsMixedOfWeightsAtMost` (module
`Sheaf.LinearAlgebra.FrobeniusModuleWeights`), `WeilConjectures.ordinaryCompactCohomology`
(module `Sheaf.Paper.OrdinaryCompactCohomology`),
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` (module
`WeilConjectures.DeligneLaumon.Reduction.Weights`), `WeilConjectures.sfWeilComplex` (module
`Sheaf.Paper.SfWeilSheafComplex`), `AlgebraicGeometry.Scheme.LisseIntegralSheaf` (module
`Sheaf.Paper.LisseAdicSheaves`), `WeilConjectures.FiniteFieldDatum` (module
`Sheaf.Paper.FiniteFieldFiber`), and the convention node
`def-weil-scheme-morphism-properties`, which deliberately has no declaration. The theorem
uses the upstream `WeilSheaf` and Frobenius-module interfaces that express these notions in
its conclusion and hypotheses.

Edge cases checked: the conclusion uses the full real parameter `w`, so weight-zero and
nonzero weights are both included; `FrobeniusModule.IsPureOfWeightOver` is vacuous for the
zero cohomology module, matching the node's zero-module clause; no nonemptiness or rational
point hypothesis is added, so geometrically connected curves without a rational point remain
included; and the smooth relative-dimension-one class supplies the finite-type and separated
instances needed by compactly supported cohomology.

Searches made before writing:

- `msearch.py Q75 lem-a1-affine-hc2-pure leanfinder "Top compact support cohomology of a pure lisse sheaf on a curve has weight w+2"`: hits were unrelated sheaf/cohomology and representation declarations; no exact match.
- `msearch.py Q75 lem-a1-affine-hc2-pure loogle "Frobenius, IsPure"`: only purely inseparable Frobenius declarations; no match.
- `msearch.py Q75 lem-a1-affine-hc2-pure grep "WeilSheaf|FrobeniusModule|compactlySupportedCohomology|IsPureOfWeight"`: no exact theorem for this generalized statement.
- `rg -n "affine-hc2-pure|isPureOfWeightOver_compactlySupportedCohomology_two" /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: found the existing weight-zero specialization
  `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine` in
  `WeilConjectures/DeligneLaumon/Reduction/RelativeAffineLine.lean`, which does not state
  the present arbitrary-weight, geometrically-connected theorem.
- `rg -n "isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine_geometricallyConnected"`
  over the source and project: no existing declaration.
- `grep -rl "lem-a1-affine-hc2-pure" dag/nodes`: found only this node and its proof references;
  no duplicate definition node.

The module compiles cleanly with `scompile.py`; the only expected warning is suppressed by
`set_option warn.sorry false`.

## Second reading by Q75

I reread the node and module together. The four structural hypotheses are represented by the
`Over`, `IsAffine`, `SmoothOfRelativeDimension 1`, and `GeometricallyConnected` instance
binders; the lisse sheaf and punctual-purity hypotheses are `hF` and `hpure`; and the degree-two
compactly supported cohomology and weight shift `w + 2` appear verbatim in the conclusion.
The inserted `haveI` only derives the finite-type smooth instance required to form compact
cohomology and does not add a mathematical hypothesis. The zero-module case and curves without
rational points remain covered. No node statement, dependency list, or source text was changed.

## Maintainer review correction (2026-10-18)

The search above covered only the older slopmaster2 tree. The live published library already
states this node verbatim: `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.isPureOfWeightOver_compactlySupportedCohomology_two`
in `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` (docstring tag
`(blueprint: lem-a1-affine-hc2-pure)`, also listed in the node's `lean_audit`). It has the same
binders, instances, `haveI` and conclusion as the delivered theorem; an `nt_compile.py` probe
closes the delivered signature with `exact` of the upstream theorem. Under delivery-errors H4 the
item is recorded as `existing: true` (branch `slopmaster2`) and the module
`lean/Sheaf/DeligneLaumon/Reduction/AffineHc2Pure.lean` is left out. The mathematical reading of
the hypotheses and conclusion given above holds unchanged for the existing declaration.
