# lem-pur-chart-diagonal-source-mate (Q58)

## Worker report

The delivery states `chartDiagonalSourceMate` in
`Sheaf.Paper.ChartDiagonalSourceMate`, namespace
`WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate`.
The natural-language statement is unchanged. The returned H2 ownership fault is repaired below. The module contains real definitions
of the specified arrows, not arbitrary arrows with the correct endpoints. Its only
two postponed proofs are `productGeometry` (the product/projection clause of this
node) and `chartDiagonalSourceMate` (the mate equation and open restriction clause).
Each has its source, blueprint ownership and complete proof plan in its docstring.

Source read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md`, Steps 1 and 3;
the node's six-step mate calculation was also read in full. Step 1 removes the
other components of U times_A U, and Step 3 composes exceptional adjunctions and
uses the canonical etale identification. No orientation or purity isomorphism
is chosen by this delivery.

### Hypotheses, one by one

* The algebraic closure of a finite field, coefficient prime different from its
  characteristic, positive n, and finite coefficient quotient are the fields of
  `P : PurityFiniteSetting.{u}` and its `P.Coefficient`. The finite stage is used
  throughout. `_hE : P.extension = ⊥` is exactly E = Q_ell, not a restriction on n.
* `U Y : Scheme.{u}` permits arbitrary schemes in the project's scheme universe.
  `[IsAffine Y]` is the affine-base hypothesis.
* `aY : Y ⟶ Spec (.of P.field.k)`, `[LocallyOfFiniteType aY]` and
  `[QuasiCompact aY]` express finite type over k. The structural map of U is
  `h ≫ aY`, so its finite type is a consequence of these and finite type of h.
  No independent k-structure or compatibility assumption is added.
* `d : ℕ` includes d = 0. `[SmoothOfRelativeDimension d h]` is smoothness of pure
  relative dimension d. `[IsSeparated h]`, `[LocallyOfFiniteType h]`, and
  `[QuasiCompact h]` express the stated separated finite-type domain.
* `AffineSpace (ULift.{u} (Fin d)) Y` is A. Its projection `↘ Y` is p.
  `e : U ⟶ A`, `[Etale e]`, and
  `w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h` express the etale Y-chart.
  Neither surjectivity of e nor separatedness over the field is assumed.
* No compactification, Noetherianity, auxiliary inverse map, orientation or
  isomorphism is a hypothesis. `Dnc.compactifiable` (Nagata) and `P.noetherian`
  discharge the geometric admissibility conditions inside definitions.
* The conclusion quantifies over `N : Etale.EtaleCompactSupportNormalization
  P.Coefficient`. This is the published proper/sum normalization datum, which
  exists by `nonempty_etaleCompactSupportNormalization`. It is not a hypothesis
  supplying the desired comparison. Its adjunction normalization uniquely fixes
  locality, and the conclusion holds for every such datum.

### Objects, maps and clauses, one by one

* W and W_A are exactly `pullback h h` and `pullback p p`. Their projections and
  closed diagonals are Mathlib's `pullback.fst`, `pullback.snd`, and
  `pullback.diagonal`. `ChartFactors.selfMap d h e w` is the published e times e.
* `productGeometry` states that self-map is etale, separated and quasi-compact,
  and states BOTH first- and second-projection identities and the diagonal
  identity. Together with w these are precisely the compatibility equations in
  the node. Restricting them along any open inclusion gives the two equations
  for q. These facts follow from the same product geometry, not a new assumption.
* `neighbourhoodCarrier` is the complement of the image of the complement of
  `Set.range (pullback.diagonal e)` under the canonical map
  U times_A U -> U times_Y U. Thus it is exactly W minus (Z minus Delta_U(U)).
  `IsCompatible` asserts that this set is an open O, and supplies its diagonal
  factorization sO with `hsO : sO ≫ O.ι = pullback.diagonal h`.
  No arbitrary smaller neighbourhood is substituted for the prescribed O.
* `Etale.dualizingComplex` is the exceptional image of the coefficient unit.
  `alpha` specializes the recorded `P.diagonalComparedRestriction` to
  `asIso (Etale.dualizingComplexBaseChangeMap ... .flip)`. Invertibility comes
  from `P.comparedDiagonalBaseChange`. This is inverse beta restricted to the
  diagonal, including the section identity, exactly the specified alpha.
* `target` is c_e in ordinary-etale coordinates. It first identifies h with e p,
  then inverts `tensorMateEtalePrecompLocalityIso` at the unit and uses the
  canonical exact/derived etale pullback comparison. This is exceptional
  composition followed by normalized Re! = Le*, with no choice of an
  endpoint isomorphism. `targetProEtale` transports this arrow by the published
  comparison functor and `Dnc.pullComparison`.
* Section objects use the already published `Dnc.sourceSection` and
  `ChartFactors.source`, and their ordinary presentation uses
  `Etale.sectionInvariant`. `Dnc.sourceComparison` provides the specified
  site comparison. This is the ModuleCat finite-coefficient presentation already
  used by the recorded diagonal-base-change interface, with its actual
  pro-etale source object, rather than a new definition of the section invariant.
  The recorded intrinsic finite section interface is also imported. Coefficient
  and site universes are retained: schemes are at u and ModuleCat coefficients
  and module objects at u+1; no equality of independent universes is imposed.
* `alphaProEtale` is sourceComparison followed by comparison of `alpha`.
  `IsCompatible` first asserts the equality of actual pro-etale morphisms
  `source.hom ≫ Le*.map alpha_p.hom = alpha_h.hom ≫ targetProEtale.hom`.
  Composition in Lean is left to right, so this is exactly
  (Le* alpha_p) after a = c_e after alpha_h.
* `viaQ` constructs a through the actual i and q on O. With
  v = i followed by p_U and q = i followed by selfMap, it uses
  `wq : q ≫ p_A = v ≫ e` and `sd : sO ≫ q = e ≫ Delta_A`.
  Its q-locality comparison is `tensorMateEtalePrecompLocalityIso`; equality
  of the two composites is transported by the conjugate of the canonical
  lower-shriek congruence. There is no arbitrary comparison of exceptional
  adjoints inserted at that step.
* The essential target-etale unit is explicit as `targetUnit`:
  c_(v,e) followed by Rv!(eta_e). Here eta_e comes from the UNIQUE normalized
  adjunction comparison, followed by the canonical pullback-unit isomorphism.
  Choosing from this uniqueness is permitted and fixes the arrow completely.
  `IsCompatible` asserts it is invertible on O, and `viaQ` uses its `asIso`.
  The inverse-direction composite is pullback coherence, q-locality, this unit,
  and inverse open locality. `viaQ` inverts that composite to obtain a.
* The conclusion identifies this `viaQ` with the already published
  `ChartFactors.sourceOrdinary`. Consequently the pro-etale equation uses
  precisely the open/q comparison, transported by canonical site comparison.
* For every `V ≤ O` and every section factorization sV through V, the conclusion
  supplies invertibility of the SAME targetUnit on V and equates `viaQ` on V to
  `viaQ` on O. This is the stated unchanged comparison after any further open
  restriction near the diagonal. V need not be affine or nonempty.

### Dependencies read and used

The recorded source declarations and docstrings were read. Mathlib matches are
used directly, without new copies. The statement-level interfaces are:

* `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
* `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
* `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
* `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
* `def-pur-section-invariant`: `Sheaf.Paper.PuritySectionInvariantIntrinsic`, `WeilConjectures.PurityFiniteSetting.sectionInvariantFinite`.
* `lem-pur-diagonal-base-change`: `Sheaf.Paper.PurityDiagonalBaseChangeCompared`, `WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange`.
* `thm-nagata-compactification`: `WeilConjectures.Compactification.NagataCompactification`, `AlgebraicGeometry.NagataCompactification`.
* `lem-amb-etale-adjoint-locality`: `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, `AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`.
* `lem-pur-co-smooth-etale-locality`: `Sheaf.Paper.CohomologicalSmoothEtaleLocality`, `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_surjective_etale`.
* `thm-pur-cohomological-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessTheorem`, `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_smooth`.
* `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`.
* `def-weil-scheme-morphism-properties`: convention collecting the existing Mathlib morphism properties.
* `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
* `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
* `def-sbc-affine-space`: `Mathlib/AlgebraicGeometry/AffineSpace.lean`, `AlgebraicGeometry.AffineSpace`.
* `def-pur-diagonal-dnc-chart-data`: `Sheaf.Paper.DiagonalDncChartNormalization`, `WeilConjectures.PurityFiniteSetting.chartDiagonalAlpha`.
* `def-pur-chart-source-comparison`: `Sheaf.Paper.ChartDncVectorFactors`,
  `ChartFactors.selfMap`, `sourceLift`, `sourceOrdinary`, `source`, with their
  required projection and geometry typing facts.

The statement cites `def-pur-diagonal-dnc-chart-data` for
`chartSectionEtaleRestriction`, `def-sp-etale-compact-support-normalization` for
N, and the four definition owners documented in the repair section below. The
chart-vector theorem and the DNC-invariance theorem conclusions are not used.
The published modules still supply these declarations at their original names.

The proof imports are the nodes in the existing six-step proof: etale left
comparison and its base-change compatibility; unbounded compact-support
comparisons; pullback composition; finite etale dualizing normalization;
finite-site counit and projection transport; smooth base change; compact-support
composition; and the proper/sum normalization. Their public maps used here are
`Etale.tensorMateEtalePrecompLocalityIso`,
`Etale.unboundedEtaleLowerShriekCongr`,
`ProEtale.smoothExceptionalCompIso`, and
`Etale.leftDerivedUpperStarComp`. The ordinary iso used in targetUnit is the
unique one characterized by `N.adjunction`, not a bare Nonempty iso.

### Edge cases and mathematical checks

* Identity chart: the self-map and q are identity comparisons, the removed set
  is empty, and the equation reduces to coherence of the same diagonal mate.
* d = 0: the coordinate type is empty, p is the canonical rank-zero affine
  projection, and h is etale. The off-diagonal components of U times_Y U still
  matter; the formula removes precisely them before restriction. No positive
  relative dimension or connectedness is assumed.
* An etale chart with multiple sheets: the complement uses the diagonal of e
  INSIDE U times_A U, rather than discarding all of Z. Thus it retains the
  actual diagonal and removes only the unwanted sheets.
* Empty U, empty Y, and empty admissible smaller neighbourhoods are permitted.
  No inhabitant or geometric point is chosen; all comparisons and equalities
  remain defined. With U nonempty a section through an empty V cannot be given,
  as required by the quantified section condition.
* Arbitrary positive n is included, including n = 1. Characteristic ell is
  excluded by P exactly as in the source. n = 0 is excluded by P.level_pos.
* The target arrow needs D_v because p_A q = e v, rather than p_A q = v.
  Omitting it would be ill-typed and would fail to represent the prescribed
  comparison. Both projections are retained in productGeometry, including the
  second projection used by the diagonal alpha.
* Shrinking imposes no new etale surjectivity, affineness or purity datum. It
  only quantifies over smaller open neighbourhoods with their diagonal lift.

No STATEMENT-DISPUTED issue or source correction was found. No new independent
notion and no dependency-record repair was required.

### Searches and validation

The following searches were performed before introducing the statement:

* `msearch.py ... leanfinder`, query "The diagonal section dualizing base change
  isomorphism commutes with etale coordinate pullback and composition of
  exceptional adjoints": eight geometric pullback/diagonal and differential
  results, no declaration asserting this mate equation.
* `msearch.py ... loogle`, query
  "dualizingComplexBaseChangeMap, etaleAmbientAdjointLocalityIso": no match
  (these project identifiers are not in the remote Mathlib index).
* `msearch.py ... grep`, query
  "dualizingComplexBaseChange|etaleAmbientAdjointLocality", CategoryTheory:
  no Mathlib match.
* `msearch.py ... leansearch`, query "etale chart diagonal dualizing counit mate
  compatibility": eight generic adjunction/mate results, no exact statement.
* `rg` of WeilConjectures and Sheaf for the item id and the source/diagonal/mate
  terminology: existing normalization and chart helpers found and reused;
  `DiagonalOrientationCharts` cites the item in its docstring but does not state
  this comparison theorem. No exact existing declaration was found.
* The current blueprint, the node and its stmt_deps, and full signatures and
  docstrings of the recorded interfaces were read. Every variable and universe
  is explicitly bound with autoImplicit false.
* `scompile.py Q58 lem-pur-chart-diagonal-source-mate` compiled the module both
  as a sandbox module and by its library name, against the live server sources.
  Both passed with no errors or non-sorry warnings. Final delivery validation
  is performed by deliver2.py, including its server preflight and recompilation.

## New nodes

Four definition nodes record existing published declarations, with existing:true,
no source move and no duplicate module:

* `def-pur-chart-source-comparison`: `ChartFactors.selfMap`, `selfMap_fst`,
  `sourceLift`, `sourceLift_geometry`, `sourceOrdinary`, and `source` in
  `Sheaf.Paper.ChartDncVectorFactors`. Its statement records the product and
  section constructions and the typing facts actually required by their data.
* `def-pur-etale-exceptional-precomp-locality`:
  `Etale.tensorMateEtalePrecompLocalityIso` in
  `Sheaf.SmoothPurity.TensorMateEtalePrecomp`. It is the conjugate of the
  normalized left comparison under the specified adjunctions.
* `def-pur-compact-support-morphism-congruence`:
  `Etale.unboundedEtaleLowerShriekCongr` in
  `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`. It is
  equality elimination with reflexive value Iso.refl, not a comparison theorem.
* `def-pur-section-pullback-site-comparisons`: `Dnc.pullComparison` and
  `Dnc.sourceComparison` in `Sheaf.Paper.PurityDncInvariance`. The first composes
  the exact/derived site pullback comparisons; the second specializes the
  already recorded `Dnc.sectionComparison` from
  `def-pur-finite-section-comparison` to the smooth source-section presentation.

All four are cited by the item. Each node includes the exact existing signature,
full defining description, original module and declarations, current blueprint
source place, import_flags:[], search results, and required creation metadata.
Their statement dependencies cite their actual primitives and typing facts.

## Dependency modules

None. No published source is moved or edited. The item's public imports now
explicitly expose the helper-owning modules; the theorem and every defined arrow
remain mathematically unchanged.

## Repair of returned delivery 28bbd8b6d51c — H2

The immutable-head review accepted the mathematics, but found that plain statement
helpers were charged to theorem nodes whose conclusions were unused. Every
requested ownership repair has been made:

1. `lem-pur-chart-dnc-vector-factors` is removed from the sandbox item's stmt_deps
   and replaced by the new `def-pur-chart-source-comparison`. No call to its
   `Conclusion` or `chart_dnc_vector_factors` theorem is introduced.
2. The already landed `def-sp-etale-compact-support-normalization` is now an
   explicit stmt_dep for `EtaleCompactSupportNormalization`.
3. `def-pur-etale-exceptional-precomp-locality` owns the published locality iso
   and is cited as a stmt_dep, rather than citing its unused tensor theorem.
4. `def-pur-compact-support-morphism-congruence` owns the actual congruence used
   in viaQ and is cited as a stmt_dep. The unbounded comparison theorem remains
   an unchanged proof dependency of the original six-step proof.
5. `def-pur-section-pullback-site-comparisons` owns the two site comparison
   arrows used in alphaProEtale, targetProEtale, and ChartFactors.source. Its
   owner is cited instead of the unused DNC-invariance conclusion.

The original main-branch stmt_deps are retained, including the expressly accepted
`lem-pur-diagonal-base-change` (whose IsIso conclusion is needed for asIso) and
`thm-pur-cohomological-smoothness`. The item was reconstructed from the current
main node, preserving every field except lean and the authorized stmt_deps
additions. Compared to the returned sandbox, only definition ownership metadata,
explicit public helper imports, the date/note, and this report have changed.
No statement correction or dependency statement alteration is required.

Searches for the new owners: msearch LeanSearch, query "Canonical etale chart
self-product section comparison, exceptional adjoint locality, compact-support
congruence and etale pro-etale pullback comparison" returned eight generic
geometric etale results; Loogle "pullback.map, conjugateIsoEquiv" returned zero
(unknown Mathlib index identifier); Mathlib grep of the six helper names returned
zero. The literal results are copied into every new node's mathlib_searches.
Exact-name rg across dag/nodes and the two Lean source trees found the four
published definition sites but no definition ownership node. The existing
finite section comparison node owns the underlying sectionComparison, which
is reused as a dependency rather than duplicated. blueprint_refs searches
returned 0 chart source, 2 generic etale locality, 0 compact support congruence,
and 1 section comparison (the parent chart blueprint unit).

Source checks reread the full signatures, data and docstrings for all named
helpers. The existing geometry facts are typing support for sourceLift and
sourceOrdinary, not chart-vector theorem conclusions. The new records are
existing:true and are compiler-probed by deliver2. The only delivered Lean
module is still the item module. The required scompile, dry-run preflight and
final delivery checks are repeated for this repaired packet.

Repair validation: scompile.py passed both sandbox and library-name compilation
(32.5 s and 34.8 s reported), without errors or non-sorry warnings. Each new
lean.statement is verbatim in the published module, every statement citation
matches stmt_deps, and no new owner reaches this consumer through statement or
proof dependencies. The repaired dry run also compiles the existing-name probes.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
