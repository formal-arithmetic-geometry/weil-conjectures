## Worker report

The delivery states `lem-coef-dualizing-closed-chart` in
`Sheaf.Paper.CoefDualizingClosedChart`. The only postponed proof is
`AlgebraicGeometry.Etale.exists_coefDualizingClosedChart`. The helper declarations
assemble the canonical bounded-below comparison and its composite counit and package
the clauses of this same node; they are not independent mathematical notions.
Definitions have real bodies. No dependency node is changed and no new node is added.
The natural-language node statement and proof are preserved.

Source read: main-20261015, `sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-finite-dualizing.proof.md`, paragraph 2 (the affine embedding and composition
of ambient adjoints) and paragraph 3 (the structural counit normalization).
The eight steps of the reviewed DAG proof are carried into the theorem docstring.

The hypotheses and clauses have the following translations.

- The fixed algebraic closure of the finite field is `D : FiniteFieldDatum`; its
  `k`, `p`, `q`, finite base field and algebraic-closure structure are the recorded
  dependency's existing data. The characteristic prime is determined by those data.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]`, with `_hl : l ≠ D.p`.
  The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]`. Its valuation ring and uniformizer are exactly
  the existing `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`, and its quotient at level j is
  `Padic.coefficientExtensionRing l E j`; no coefficient ring is redefined.
- `m n : ℕ`, `hm : 1 ≤ m`, and `hmn : m ≤ n` render `1 ≤ m ≤ n`.
  Positivity at level n is the explicit proof `hm.trans hmn`.
- `(Y : Scheme) (aY : Y ⟶ Spec (.of D.k))` is the k-scheme and its structural map;
  `[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]` are separated finite
  type, precisely the conjunction in the recorded finite-type dependency.
  `[IsAffine Y]` is the additional affine hypothesis.
- The conclusion existentially quantifies `r : ℕ` and the embedding
  `i : Y ⟶ AffineSpace (ULift (Fin r)) (Spec (.of D.k))`.
  `IsClosedImmersion i` is Mathlib's recorded closed immersion. The equality
  `i ≫ (AffineSpace ... ↘ Spec (.of D.k)) = aY` is the factorization `pi = aY`.
  `IsFinite i ∧ IsProper i ∧ LocallyOfFiniteType i ∧ QuasiCompact i` explicitly
  renders finite, proper and finite type.
- `CoefClosedChartAt ... m ... ∧ CoefClosedChartAt ... n ...` supplies the same
  chart simultaneously at B and A. It installs the proved coefficient finiteness
  and the compactifications implied by the geometric hypotheses, rather than
  asking for them as inputs. The coefficients are lifted to `Type (u+1)` using
  `ULift`, the ordinary small-etale size convention already used by the recorded
  boundary-adjunction dependency; this is an equivalent copy of the same ring.
- `DerivedCategoryModule R T` is the recorded ordinary unbounded derived category
  of `Sheaf T.smallEtaleTopology (ModuleCat R)`. `constantComplex R s` is R in
  degree zero. `rightDerivedLowerShriek` is F, `rightDerivedUpperShriekAdjunction`
  is F ⊣ G, and `dualizingComplex` is exactly G applied to this coefficient unit.
  The epsilon maps are those very adjunction counits, not extra supplied maps.
- The inherited notation T, c, and bounded constructible finite-Tor is background
  notation, with no quantified K and no hypothesis or assertion about these maps
  in this node's conclusion. Its exact recorded definitions are imported:
  `derivedTensor`, `CoefficientTensorModel`, `compactSupportCoefficientComparisonPlus`,
  `DerivedCategory.isBoundedConstructible`, and `DerivedCategory.hasTorAmplitudeIn`.
  In particular finite-Tor is not imposed on inputs to closed pushforward.
- `CoefClosedChartProperties.exact_limits` and `.exact_colimits` express exactness
  of ordinary module-sheaf closed pushforward. `.identity_open` identifies the
  actual `rightDerivedLowerShriekOfCompactification` for
  `Compactification.ofIsProper i` (whose open part is literally `𝟙 Y`) with
  `lowerStar.mapDerivedCategory`. `.derived_pushforward` identifies Ri* with the
  same termwise functor on the whole unbounded derived categories.
- `.cohomology` is a natural isomorphism in every integer degree q between
  Ri* followed by H^q and H^q followed by ordinary i*. This retains the derived
  isomorphism as well as its per-degree consequence.
- `.closed_boundedBelow` states that I, the right adjoint supplied by the closed
  ambient dependency, takes every bounded-below L to a bounded-below object.
- `.omegaY_boundedBelow`, `.omegaP_boundedBelow`, and
  `.closed_omegaP_boundedBelow` record lower bounds before making any coefficient
  comparison: in particular both representing objects omegaY and I omegaP are
  bounded below, without assuming coefficient-change invertibility.
- `coefClosedChartPlusPushforwardIso` uses the identity-open compactification
  and the recorded canonical refinement iso to identify bounded-below Ri* with
  Ri!. `coefClosedChartComposition` then uses precisely
  `rightDerivedLowerShriekPlusCompIso`, transports the factorization equality,
  and uses the existing ambient/Plus compatibility isomorphisms. Its domain is
  D+, so no extra unbounded composition theorem is asserted or assumed.
- `CoefClosedChartNormalization` asserts a unique isomorphism theta from omegaY to I omegaP
  whose composite with this canonical composition comparison satisfies
  epsilonY = epsilonP after Fp(e) and the image of theta. The helper
  `coefClosedChartCompositeCounit` expands the closed counit and that exact
  comparison into the displayed morphism. Uniqueness fixes the canonical,
  counit-compatible identification promised by the source.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  coefficient convention. `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `DerivedCategoryModule`, `constantComplex`, `DerivedCategory.hasTorAmplitudeIn`;
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: `DerivedCategory.hasTorAmplitudeGE`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`;
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `DerivedCategory.isBoundedConstructible`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`, and
  their Plus variants and compatibility isomorphisms.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons` and its recorded
  existing API in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerShriekOfCompactificationPlusIso`,
  `rightDerivedLowerShriekPlusCompIso`, `rightDerivedLowerShriekPlusCongr`,
  `openImmersionLowerShriekId`. All are the existing canonical maps.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`:
  `rightDerivedUpperShriekAdjunction`;
  `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`: `dualizingComplex`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp` and its composite
  counit formula. `Mathlib.CategoryTheory.Adjunction.Unique` supplies uniqueness.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`:
  `CoefficientTensorModel` and `compactSupportCoefficientComparisonPlus`.

The proof dependencies with existing modules are imported privately, including
`BoundaryEtaleAdjunctionRestriction`, `EtaleSupportedKernelAdjunction`,
`AffineFiniteTypeAlgebra`, `ExactDerivedAdjunctionBounds`, `RingedSiteModules`,
and the Mathlib exact-functor/cohomology and geometric criteria. Public imports
are the interfaces used by the statement and the concrete canonical constructions.

Edge cases checked against the source and the formulation: the zero ring and
empty Y remain allowed; `r = 0` uses the empty coordinate type and is not excluded;
`m = n` repeats the identical coefficient stage; the minimum level `m = n = 1`
is included; Y need not be smooth, reduced, connected or regular; the input of
closed pushforward may be unbounded with no constructibility or Tor hypothesis;
all q are integers. No lower bound on an exceptional object is an input.

Searches for an existing statement:

- `msearch.py leanfinder`, query “Affine closed immersion into affine space exact
  etale direct image and dualizing objects compose right adjoints”: 8 hits, all
  affine-space/Spec geometry (`AffineSpace.homOfVector`, `GammaSpecAdjunction`,
  affine-space/Spec equivalences); none contains the derived adjunction or counit
  clauses, so no exact match.
- `msearch.py loogle`, query `AlgebraicGeometry.IsClosedImmersion,
  CategoryTheory.Adjunction.comp`: 0 hits.
- `msearch.py grep`, query `dualizing|ClosedChart`, directory `AlgebraicGeometry`:
  0 Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, query
  `dualizingClosed|dualizing_closed|closedChart|closed_chart|lem-coef-dualizing-closed-chart`:
  the nearby closed-chart preservation theorem concerns constructible finite-Tor
  exceptional preservation and smooth purity; it does not state this chart
  existence and structural dualizing normalization. No exact declaration matches.
- A further `rg` of `dualizingComplex` found the existing upstream dualizing
  construction, which is reused directly. Exactness and termwise direct image
  likewise reuse the existing finite direct-image and exact-derived APIs.

No statement dispute or source correction was needed. The previous worker's
stage-1 PASS is distinguished from the absent stage-2 Lean binding; this delivery
supplies the latter.

Compiler diagnosis: the normalization initially occurred as a dependent field of
`CoefClosedChartProperties`. Lean's generated structure machinery repeatedly
unfolded the derived monoidal unit while checking that field and timed out.
It is now an ordinary Prop-valued definition, with the independently supplied
bound used to evaluate the same comparison. The bounds record and this predicate
are existentially conjoined in `CoefClosedChartAt`; neither content nor hypotheses
change. The normal module has no heartbeat or timeout override. The isolated
comparison, bounds, and normalization checks compile.

Validation: the complete delivered module compiled cleanly with `scompile.py`
against the live published server build, in both sandbox and library module modes
(8.9 s and 8.2 s), within the unchanged 60-second per-file limit. No warnings
or errors were reported. Every variable and universe is explicitly bound and
`autoImplicit` is disabled. The seven public declarations are recorded in `lean`.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
