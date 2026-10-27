## Worker report

Repair of the returned delivery at immutable head `ec84215e340f`: replace the
semilinear theorem dependency with its existing definition owner. The Lean module
is unchanged from that reviewed head; its earlier F1–F7 repairs are retained. The delivery owns one module,
`Sheaf.Paper.PoincareDualityConventions`, with primary declaration
`WeilConjectures.PoincareDualityConventions`. Its namespace declarations are listed
in `lean.declarations`. All are actual definitions or proved instance constructions;
there are no new postponed theorems and no `sorry` in this module.

Source read: the complete current blueprint unit at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-cor-sp-all-coefficients/def-pod-conventions.md`,
the node statement and `blueprint_update`, and the recorded interfaces of its
statement dependencies. The current source's point categories are exposed as
`finitePointCtf`, `integralPointCtf`, `rationalPointCtf`, and `qbarPointCtf`.
The older module-complex presentations are also exposed, without asserting that
finite cohomology alone implies finite Tor amplitude.

The hypotheses and setting are rendered individually as follows.

* `datum : FiniteFieldDatum` supplies the prime p, positive exponent, q=p^a,
  finite field k₀, fixed algebraic closure k and its inclusion.
* `coefficients : datum.CoefficientDatum` supplies ℓ, its primality and ℓ≠p,
  and the fixed algebraic closure Qlbar of Qℓ.
* `extension : Padic.FiniteCoefficientFields coefficients.l coefficients.Qbar`
  is the actual finite subextension E⊂Qlbar. Its `val` is used consistently for
  the finite, integral and rational conventions. The valuation ring and
  uniformizer are the dependency's `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`. The ring `coefficientRing` is literally
  `Padic.coefficientExtensionRing ... extension.val level`.
* `level : ℕ` and `level_pos : 1 ≤ level` give the positive exponent n.
* `X₀ : Over (Spec (.of datum.k₀))` is the k₀-model. `finite_type` and
  `quasi_compact` together express finite type. `separated` expresses separatedness.
* `d : ℕ` and `smooth : SmoothOfRelativeDimension d X₀.hom` express smoothness
  of pure dimension d, including d=0. `geometrically_connected` is the recorded
  `GeometricallyConnected X₀.hom`, not just connectedness of rational points.
* `X`, `s`, and `structureMap` are the actual geometric fibre, Spec k and its
  structure morphism. The geometric instances transport the stated properties
  along this base change, with no extra hypotheses.
* `exceptional_adjoint_admissible` requires, for every `n` and `hn : 1 ≤ n`,
  `poincareExceptionalAdmissibility ... n hn`. The latter unfolds to
  `IsExceptionalAdjointAdmissibleAtFiniteStage` for this very structure morphism,
  the actual E, and `HasCompactification.compactification f`. It constructs the
  coefficient-prime unit map by the stalk germ and supplies finite-type geometry.
  It is a real admissibility proposition, not an arbitrary Prop-valued field.
  There is one chosen compactification, not a hypothesis quantified over all of them.
* No field asserts properness. No identification of ordinary and compact-support
  sections is imposed.

Every operation clause is rendered as follows. All unqualified names in this list
belong to `WeilConjectures.PoincareDualityConventions`.

* The four constructible categories are `finiteTorCategory`, `integralCategory`,
  `rationalCategory`, and `qbarCategory`. They reuse `finiteTorConstructibleCategory`,
  `sfIntegralConstructibleCategory`, `sfRationalConstructibleCategory`, and
  `generalAlgebraicallyClosedConstructibleCategory` on the actual small pro-etale
  site, preserving its object/morphism universe distinction.
* Finite pullback, tensor and internal Hom are `derivedPullback`, `derivedTensor`,
  and `derivedInternalHom`, using the recorded finite constructors at
  `level-1`; `level_pos` identifies `(level-1)+1` with level. The higher pullbacks
  and tensors are `integralPullback`/`integralTensor`,
  `rationalPullback`/`rationalTensor`, and `qbarPullback`/`qbarTensor`.
  Higher internal Hom is used explicitly in the coefficient and Verdier duals.
* `finiteDirectImage`, `integralDirectImage`, `rationalDirectImage`, and
  `qbarDirectImage` expose Rf_*. The integral functor is the recorded completed
  direct image. The rational functor is the actual linear integral direct image
  extended by `ScalarLocalization.extension`; the common-stage functor is
  `geometricCommonStageDirectImage`. No arbitrary direct-image functor is a field.
* `finiteCompactSupport` is the recorded `sfIntrinsicCompactSupport` of a chosen
  compactification. `finiteExceptionalInverseImage` calls the published
  `Scheme.finiteExceptionalInverseImage`, the etale right adjoint transported
  through the comparison site. It does not extract data from the admissibility
  existential.
* `coefficientOperation` exposes the complete recorded
  `ConstructibleExceptionalCoefficients.System.ring.operation` for a general
  separated finite-type morphism and chosen compactification. `exceptionalOperation`
  specializes it to a_X. Its `.F`, `.G`, and `.adjunction` retain the source's
  Rf_!, Rf^! and their unit/counit adjunction, including its scalar and proper/open
  normalizations. `integralCompactSupport`/`integralExceptionalInverseImage`,
  `rationalCompactSupport`/`rationalExceptionalInverseImage`, and
  `qbarCompactSupport`/`qbarExceptionalInverseImage` project these exact operations.
  Their system argument is the full recorded normalized system, not a bare pair
  of functors or a freely chosen adjunction.
* `finiteDualizingObject` is the canonical intrinsic realization of
  `puritySetting.diagonalDualizing structureMap`, whose definition is precisely
  the recorded finite exceptional inverse image of the comparison-origin
  coefficient unit. `integralDualizingObject`, `rationalDualizingObject` and
  `qbarDualizingObject` apply the corresponding operation's `.G` to its own
  degree-zero, twist-zero coefficient unit. Thus these are ω_X=Ra_X^!Λ.
* `finiteOrientation` maps the canonical
  `PurityFiniteSetting.diagonalDualizingObject d structureMap (𝟙 s)` through the
  specified intrinsic realization equivalence. Its source is exactly
  `finiteDualizingObject`, also named `finiteOrientedDualizingObject`.
  `integralOrientation`, `rationalOrientation`, and `qbarOrientation` are the
  actual `AdicSmoothDualizing.integralIdentification`, `rationalIdentification`,
  and `closedIdentification` for the same system and same dualizing objects.
  These are the owners' normalized η_X:ω_X≅Λ_X(d)[2d], not supplied isomorphisms.
* For each prefix `finite`, `integral`, `rational`, and `qbar`, the four names
  `<prefix>OrdinarySections`, `<prefix>CompactSections`,
  `<prefix>OrdinaryCohomology`, and `<prefix>CompactCohomology` directly specialize
  the recorded RΓ, RΓ_c, H^i and H_c^i constructions to X. Every integer degree
  and the source's compactification parameters are retained.
* `finiteTwist` is derived tensor with the degree-zero coefficient twist;
  `integralTwist`, `rationalTwist`, and `qbarTwist` are the recorded signed twisting
  functors. `twistFrobeniusNormalization` calls `Purity.tau_scalar` and
  `twistFrobeniusScalar` calls `TwistFrobeniusScalar.scalar`. These retain q^{-m}
  on Λ(m), hence q^m on Λ(-m), for arbitrary signed m.
* `finitePointCtf`, `integralPointCtf`, `rationalPointCtf` and `qbarPointCtf`
  use the same coefficient categories at s. `finitePointComplexes`,
  `integralPointComplexes`, `rationalPointComplexes` and `qbarPointComplexes`
  expose the existing module presentations, retaining finite cohomology,
  finitely generated completeness, finite dimension and common-stage data.
  `pointDual R C` is exactly `(coefficientDerivedDual R).obj (op C)`;
  it applies also with the prescribed ULift coefficient rings.
* `finiteCoefficientDual`, `integralCoefficientDual`, `rationalCoefficientDual`,
  and `qbarCoefficientDual` are the recorded internal Homs into the respective
  coefficient units. `finiteVerdierDual`, `integralVerdierDual`,
  `rationalVerdierDual`, and `qbarVerdierDual` use the same internal Homs into
  their corresponding ω_X. The rational/common-stage `HomPair` membership is
  constructed from `integral_constructible_internalHom` and
  `sfDerivedComplete_iff_legacy`, so no extra closure assumption is imposed on K.
* `strictWeilComplex` is the recorded `sfWeilComplex`. `finiteFrobenius` and
  `integralFrobenius` form the two literal composites τ followed by the ordinary
  or compact sections functor's image of φ.hom. The finite exponent is `n+1`,
  covering every positive finite stage. `globalFrobenius` calls
  `globalGeometricFrobenius` at E; `globalQbarFrobenius` calls its common-stage
  version, retaining the ordinary/compact selector. Each has an explicit
  `...OnCohomology` definition that takes the homology of that same derived map.
* `finiteCompactTransport`, `finiteCompactFrobenius`, and
  `finiteCompactFrobeniusCohomology` expose the recorded trace-formula
  `finiteGlobalCompactStep`, `finiteGlobalFrobenius ... 0` and its homology maps.
  The final index 0 is the source's m=1 clause. These use that owner's canonical
  small model of the finite field, through the separately cited computed `base`.
  The other conventions use E itself, rather than mixing these two coordinates.
* `frobeniusIterate F r hr` is `F ^ r`, the r-fold composite for r≥1. No theorem
  comparing this power with the trace-formula m=r expression is asserted here;
  that remains the separate node named by the source. The existing transport-iso
  dependency supplies invertibility of the transports; this definition introduces
  no new isomorphism assertion or proof obligation for that theorem.

Dependency declarations used (module names below have prefix `Sheaf.`):

* `Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`, `geometricFiber`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  the finite-type, quasi-compact, separated and geometrically-connected classes
  recorded by the geometric dependency nodes.
* `Paper.TraceFormulaCoefficientConventions`: `TraceFormulaCoefficientConventions`,
  `geometricBaseChange`, `structureMap` and the small-field coordinate interface.
  Its owning node `def-trf-coefficient-conventions` has been added to `stmt_deps`.
* `Paper.ExceptionalAdjointAdmissibility`:
  `IsExceptionalAdjointAdmissibleAtFiniteStage`.
* `Paper.FiniteTorAmplitudeSites` and `Paper.IntrinsicFiniteTorsionConstructibility`:
  the existing `finiteTorConstructibleCategory` and intrinsic finite predicates.
* `Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`,
  `integralDerivedPullback`, `integralDerivedTensor`, `integralDerivedInternalHom`,
  and the corresponding rational/common-stage constructors and pair predicates.
* `Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its common-stage models.
* `AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`;
  `Paper.FiniteExceptionalInverseImage`: `Scheme.finiteExceptionalInverseImage`;
  `Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, `.ring.operation`.
* `Paper.GeometricCommonStageDirectImage`: `geometricCommonStageDirectImage`;
  `Paper.SystemOperationExchangeRealization`: `FrobeniusExchange.directImageFunctor`,
  `directImage_linear`; `CategoryTheory.SemilinearScalarLocalization`:
  `ScalarLocalization.extension`. Its definition owner is the existing node
  `def-trf-semilinear-raw-localization-extension` (`existing: true`, landed
  2026-10-23). That node replaces `lem-pur-semilinear-scalar-localization` in
  `stmt_deps`: the item uses the extension definition, not the theorem's conclusion.
  The direct-image construction also cites its recorded realization owner.
* `Paper.PurityDiagonalDualizingObject`: `PurityFiniteSetting.diagonalDualizingObject`;
  `Paper.AdicSmoothDualizingComplexes`: `AdicSmoothDualizing.fieldStage`,
  `compactification`, the three twist units and the three canonical identifications.
* `Paper.CoefficientDuality`: `coefficientDerivedDual`;
  `Paper.IntegralConstructibleInternalHom`: `integral_constructible_internalHom`;
  `Paper.SfDerivedCompleteLegacyComparison`: `sfDerivedComplete_iff_legacy`.
  The latter two owning nodes have been added to `stmt_deps`.
* `Paper.IntrinsicCoefficientTwistsUnrestricted`: `sfIntegralTwistingFunctor`,
  `sfRationalTwistingFunctor`, `sfQbarTwistingFunctor`;
  `Paper.PurityTateDatum`: `Purity.tau_scalar`;
  `Paper.TwistFrobeniusScalar`: `TwistFrobeniusScalar.scalar`.
* `Paper.OrdinaryCompactCohomology`: the four-coefficient ordinary/compact sections
  and cohomology constructors; `Paper.FiniteCoefficientPoint`: the point categories.
* `SixFunctors.FrobeniusCohomologyTransport`: the actual finite/integral transports
  and sections functors; `Paper.GlobalGeometricFrobenius`:
  `globalGeometricFrobenius`, `globalGeometricFrobeniusOnCohomology`,
  `globalGeometricFrobeniusQbar`, `globalGeometricFrobeniusQbarOnCohomology`;
  `Paper.TraceFormulaLocalFrobeniusOperator`: `finiteGlobalCompactStep`,
  `finiteGlobalFrobenius`, `finiteGlobalFrobeniusCohomology`;
  `Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilPrimeInvertible`.

Edge cases read through: level 1 corresponds to finite constructor index 0; every
positive exponent is permitted; dimension zero has no excluded branch; the zero
complex and every integer cohomological degree remain valid; negative twists use
the existing signed functors; the identity iterate r=1 is the original map;
ordinary and compact support remain separate; nonproper X₀ is permitted; the same
field of definition and unequal fields in the common-stage Hom pair are handled
by the recorded compositum/scalar extension. No extra universe equality is assumed.

Searches retained in `searches.jsonl`:

* `msearch.py NG def-pod-conventions leanfinder "Poincare duality conventions finite
  field coefficient smooth scheme Verdier dual"`: eight hits, finite-module duals
  and smooth-algebra results; no convention package.
* `msearch.py NG def-pod-conventions loogle "PoincareDualitySetting,
  TraceFormulaCoefficientConventions"`: zero hits, with the diagnostic that
  `PoincareDualitySetting` is not a Mathlib identifier.
* `msearch.py NG def-pod-conventions grep
  "PoincareDualityConventions|Poincare duality conventions"`: zero Mathlib hits.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the package name and
  `def-pod-conventions` found no prior matching package. The general upstream
  Poincare setting is not this definition. Further targeted `rg` searches found
  the recorded finite exceptional, purity, coefficient duality, internal-Hom
  closure and Frobenius interfaces used above; their signatures and docstrings
  were read before using them.

No new definition nodes, dependency repair modules, or statement correction are
part of this delivery. No `STATEMENT-DISPUTED` claim is made. Only `lean` and the
five additions of already recorded direct-use dependencies change on the item.

## Second reading by NG

Fresh self-reading with the node, current source and final module open; no claim
of an additional reviewer or a separate agent. The previous report's statement
that omitted orientation, point duals and compact cohomology were supplied was
false. This report supersedes it.

F1: checked the source of all four `...Orientation` terms. They call the named
purity owners, and their source objects are the same ω_X used by the duals.
The remaining finite small-model/raw-field mismatch found during this reading
was repaired: all ordinary finite operations and the finite purity object now
use `extension.val`. Only the explicitly named trace-formula aliases retain the
owner's small model, as that recorded interface requires.

F2: read `finiteExceptionalInverseImage` and each higher `.G`/`.F` projection.
No `Classical.choose` of admissibility is used. The higher system argument retains
its recorded realization and normalization data; ω_X applies that same system
operation to its coefficient unit. The generic `coefficientOperation` retains
both functors and their adjunction for arbitrary eligible f, not only a_X.
The admissibility helper now uses one chosen compactification.

F3: read `pointDual` and all eight sheaf dual definitions. The second arguments
are respectively the actual coefficient unit and the actual ω_X. Internal-Hom
pair membership is derived without a new assumption on K or an arbitrary object.

F4: checked all sixteen sections/cohomology aliases, the two finite/integral
transport composites, their degreewise maps, both higher global operators and
both support selectors. Checked that the exact recorded
`finiteGlobalCompactStep` is used, and that iteration is power, not a separately
assumed operator.

F5: the structure now states `datum`, `coefficients`, `extension`, `level`, `X₀`
and the geometric hypotheses directly. The trace-formula package is computed by
`base` and its owning node is explicitly cited.

F6: every named declaration, including the nine abbreviations singled out in the
return, has a `Source:` docstring and `(blueprint: def-pod-conventions)`. Explicit
universes and `autoImplicit false`/`relaxedAutoImplicit false` prevent implicit
new parameters. There is no definition data hole.

F7: the clause mapping above names actual declarations for orientation, point
duality and compact cohomology rather than counting imports as implementations.
There is no assertion of properness, equality of ordinary and compact sections,
or an unrecorded trace-formula iterate comparison. Compiler and delivery checks
were run on the repaired file for the previous delivery. This ownership-only
repair reruns compilation and delivery checks on the unchanged Lean module.


H2 ownership repair of `ec84215e340f`: reread the definition node
`def-trf-semilinear-raw-localization-extension`, including its `lean.declarations`,
and the full docstring and signature of `CategoryTheory.ScalarLocalization.extension`
in `Sheaf.CategoryTheory.SemilinearScalarLocalization`. Its raw scalar-localization
functor is exactly the term used by `rationalDirectImage`; the corrected edge cites
this definition owner. Removed only the edge to
`lem-pur-semilinear-scalar-localization` and added that existing definition edge.
The Lean declarations, statement and other dependency edges are unchanged.
`cor-coef-integral-internal-hom` and `lem-sf-derived-complete-legacy-comparison`
remain genuine theorem dependencies: their closure conclusion and iff are used
inside `integralHomPair` to type the rational and common-stage dual constructions.
No new node or module is required.
