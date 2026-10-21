## Worker report

The module states `WeilConjectures.RawHeartAdic.raw_heart_adic_lisse_stratification`.
It contains one postponed theorem and explicit helper interfaces for precisely the
witnesses and canonical comparisons in this node. All definitions have actual data;
none chooses an unspecified object from a mere existence assertion. No node statement
or dependency record is changed, and no independent notion is introduced.

Hypotheses and conclusions, clause by clause:

- The fixed prime-power field datum is `D : FiniteFieldDatum`; the coefficient prime
  is `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`. The coefficient closure is `Ω`
  with `Field`, `Algebra ℚ_[l] Ω`, and `IsAlgClosure ℚ_[l] Ω`. The given complex
  embedding is `iota : Ω ≃+* ℂ`. It is not used in the geometric/lattice conclusion.
- `X : PerAdic.Base D.k` means a scheme over the geometric field with separated,
  locally finite-type, quasi-compact structure map. It does not require connectedness,
  reduction, smoothness, or nonemptiness. `M : sfCommonStageHeart l X.scheme Ω`
  uses the recorded raw common-stage heart, without a Karoubi envelope.
- `Strata.stage`, `finite`, and `representative` give one finite coefficient field,
  a heart representative, and its isomorphism with `M` under the recorded inclusion.
  `partition` is the existing finite locally closed scheme stratification;
  `reduced` requires every stratum reduced. `bases`, `domain`, and `base_map` carry
  exactly those schemes and their inherited finite-type structure maps.
- `Strata.model` is a normalized classical rational finite system over the same
  `stage` for every stratum. `restriction` identifies its raw realization with
  the actual `rationalDerivedPullback` of the fixed representative. The definition
  `Strata.lattice` uses the inverse of the specified completion/reduction equivalence.
  Its tower is `(model ν).obj.integral`, with ordinary finite locally free etale
  levels. The existing system predicate supplies quotient transition compatibilities;
  `Comparison.reduction`, `reduction_cokernel`, `completion_limit`, and
  `counit_projection` fix the quotient, inverse-limit and reduction maps.
- `ClassicalAt.normalized` identifies the classical rational realization with the
  H⁰ of the recorded raw lisse realization. `Comparison.rationalObject` identifies
  it with the localization of the very lattice defined above. `ClassicalAt.completed`
  composes the finite-quotient-normalized raw completion, coefficient-size transport,
  and completion of the classical tower.
- The raw sf/PBC comparison is the existing `FdCoefficientComparisonSystem`, including
  its identity on the integral category and formula on localized arrows.
  `HeartComparison.common_bounds` and `finite_bounds` identify both halves at every
  degree. The latter spells the target half as the strict image of the recorded
  integral half, avoiding a conflict between two definitionally different shift
  instances on the same PBC rational category. It is the same cohomological class.
- `HeartComparison.realization` compares the finite-stage continuous derived
  realization with the raw lisse realization. `ContinuousRational.At.integralIso`,
  `localizationIso`, and `inclusion` specify B_E and its localization, with quotient
  and scalar normalizations. `HeartComparison.fibres` compares the actual recorded
  adic geometric fibre functors at every algebraically closed geometric point.
- `CoefficientSize` fixes both lifted classical coefficient rings pointwise using
  `ULift.down` and commutes with the integral-to-rational inclusion.
  `CondensedCoefficients` uses a small normed-field presentation of the same E and
  fixes both continuous coefficient isomorphisms pointwise. Its `rationalChart` and
  `integralChart` are the existing adjoint `chartComparison` isomorphisms, with
  multiplication given by the existing `chartComparison_isMonHom`; their input is
  composition with the actual profinite test projection. Thus the maps into the
  completed ring have the finite quotient projections specified in the dependencies.
- `ClassicalAt.fully_faithful` and its natural `fibre` comparison retain all rational
  maps and adic fibres, rather than just existence of object models.
  `ClassicalFamily.pull` and `scalar` use the existing finite-system operations;
  `pull_sections` and `scalar_sections` fix them on the actual adjunction/tensor
  units, so they are the normalized comparisons, including successive operations.
  `Normalized.pull`, `field`, and `point` are the recorded raw normalizations;
  `Family.transport` gives the restriction/coprojection square for every point
  automorphism, hence every positive geometric-Frobenius iterate.
- `ClassicalCommon` uses the common-stage Hom quotient with its finite transitions
  and `transitions_normalized`. It maps fully faithfully both into the raw heart
  and into the existing `LisseAlgebraicSheaf` category. `classical_objects` and `classical_maps` fix
  its objects and finite-stage maps through `algebraicModelFunctor`; `liftedStage`
  and `liftedStageMap` are the actual intermediate-field and size equivalences.
- The Weil clause quantifies over every separated finite-type model Y₀ and every
  actual Weil complex whose carrier is the given M after the stated geometric
  identification. The piece is an actual immersion `j₀` over k_m, its geometric
  base change is `eW`, and the projection equations require that its inclusion is
  exactly that base change inside the selected stratum. These equations introduce
  no extra stability assumption. `WeilLift` gives its geometric Frobenius (both
  projections specified), a possibly larger finite stage, a rational classical
  model and isomorphism, and `realizes_iterate` equates its realization to the
  restricted `localQbarWeilIterate`. `restrictedWeil` is the explicit composite
  of the two canonical composition comparisons and that actual Weil iterate.
  No integral Frobenius map and no stability of the initial partition is assumed.
- The reduced-geometric-fibre clause supplies `Frontier`: one positive m, reduced
  closed chain beginning with the reduced finite-field model and ending with the
  empty scheme, all inclusions in the over category of that same k_m. Its open
  differences are covered disjointly by finitely many nonempty reduced affine,
  geometrically connected, smooth pieces, with dimensions in ℕ. `refinement`
  supplies their immersion into an initial stratum and its equality with the
  geometric base change of the descended inclusion; `geometric_projection` fixes
  the comparison with the original model on its projection as well. The same `ClassicalFamily.pull`
  applies to those further restrictions, so the coefficient stage and normalized
  lattices are retained. `zero_dimensional` gives an isomorphism to Spec k_m.

Dependency declarations read and used:

- `def-weil-punctual-weights`: `Sheaf.Paper.AdicPunctualWeights`, `WeilConjectures.SfIsPunctuallyPureOfWeight`.
- `def-weil-weil-sheaf-complex`: `Sheaf.Paper.SfWeilSheafComplex`, `WeilConjectures.sfWeilComplex`.
- `def-weil-constructible-standard-tstructure`: `Sheaf.Paper.SfConstructibleHeart`, `WeilConjectures.sfIntegralStandardClass`.
- `def-constructible-stratification`: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`, `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `def-pod-lisse-l-adic-sheaves`: `Sheaf.Paper.LisseIntegralSmallCoefficients`, `AlgebraicGeometry.Scheme.LisseIntegralSheafOfUniverses`.
- `lem-fd-rational-coefficient-category-comparison`: `Sheaf.Paper.RationalCoefficientCategoryComparison`, `WeilConjectures.rationalCoefficientCategoryComparison`.
- `def-weil-local-frobenius-trace`: `Sheaf.Paper.LocalFrobeniusTrace`, `WeilConjectures.localFrobeniusTrace`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-weil-pbc-scheme-reduction`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `lem-tw-lisse-rational-realization`: `Sheaf.Paper.LisseRationalRealization`, `WeilConjectures.LisseRealization.lisse_rational_realization`.
- `lem-per-continuous-rational-derived-realization`: `Sheaf.Paper.ContinuousRationalDerivedRealization`, `AlgebraicGeometry.Scheme.ContinuousRational.continuous_rational_derived_realization`.
- `def-weil-constructible-heart`: `Sheaf.Paper.SfConstructibleHeart`, `WeilConjectures.sfRationalHeart`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.

Additional recorded proof interfaces used publicly by the witness structures:
`Sheaf.Paper.AdicHeartIntrinsicFibres` (`PerAdic.Base`, `sfAdicRationalFiber`),
`Sheaf.Paper.LisseCompletedSystemComparison` (`CompletedLisse.System` and its
normalized `Comparison`/`Operation` data), and
`Sheaf.DeligneLaumon.SmoothAffineFrontierStratification`
(`smooth_affine_frontier_stratification`). The existing classical fibre functor is
reexported by `Sheaf.Paper.LisseAdicFiberFunctors`; no private fibre construction.
The module imports the recorded statement dependencies publicly and the remaining
proof dependencies privately. The theorem docstring transcribes all twelve DAG
proof steps and their cited nodes.

Edge cases checked:

- Empty X and zero M: no nonempty-base hypothesis; partition size and piece counts
  may be zero, and all finite-free ranks may be zero.
- Nonreduced X: only stratum schemes are reduced; the raw object remains on X.
- Zero-dimensional frontier pieces: the precise over-category Spec k_m iso is
  stated. Empty differences are permitted by zero piece count.
- Rank-one Weil map of nonzero valuation at Spec k: the rational map is allowed;
  no invariant lattice is requested. Coefficient enlargement is allowed for the
  map, its inverse and the common-stage identity equations.
- Further restrictions need not be Frobenius-stable until a descended k_m piece
  is considered. The initial strata have no such stability requirement.
- Coefficient universes: finite fields are canonically shrunk to the scheme universe
  for the raw interfaces and lifted by ULift for the existing classical interface.
  The classical algebraic closure is the canonical ULift of Ω. No relation between
  small-site object and morphism universes is changed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Constructible raw rational adic heart sheaves admit
  finite locally closed stratification with classical lisse integral lattices"`:
  eight unrelated locally Artinian, locally noetherian and condensed-sheaf hits;
  no raw-heart stratification theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.LisseIntegralSheaf,
  IsLocallyConstant"`: zero matches (unknown first identifier in the Mathlib index).
- `msearch.py ... grep "lisse|Lisse|[Ss]tratification" AlgebraicGeometry/Sites`:
  zero hits.
- `msearch.py ... leansearch "Constructible adic sheaf finite locally closed
  partition lisse integral lattices"`: eight topology/constructibility/partition
  and condensed-category hits, no exact statement.
- `rg` for raw-heart and lisse-stratification names in `lean/WeilConjectures` and
  `lean/Sheaf`, and the exact item id in `lean/WeilConjectures`: no existing theorem.
  Broader lisse-lattice searches found the recorded generic upstream lattice
  interfaces, which are imported instead of copied.

Validation: each iteration was compiled only by the prescribed `scompile.py` wrapper.
The final module has one expected sorry warning and no other warnings or errors.
No statement correction, disputed statement, new node, or dependency record repair.

## Second reading by NE

Author's separate rereading against the complete node, dependency signatures and
blueprint paragraphs 6--7; the maintainer supplies the independent delivery review.
I checked the hypotheses and every clause listed above with the Lean file open.
Corrections made during this reading: ordinary finite-free towers are used rather
than derived reductions of a torsion representative; the same E is retained on all
strata; geometric fibres quantify over every algebraically closed geometric point;
normalized restriction and scalar maps are constrained on actual unit sections;
the Weil equality lifts the specified iterate rather than an arbitrary isomorphism;
frontier differences retain finite disjoint piece families and the empty case.
All helper data belong to this node's witness/comparison interfaces. There is one
postponed theorem with the entire DAG proof plan, and no hollow definition.
