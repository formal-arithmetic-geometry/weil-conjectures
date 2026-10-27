## Worker report

The module `Sheaf.Paper.ConcreteProjectionReductionSquare` states
`WeilConjectures.ConcreteProjectionReduction.concreteProjectionReductionSquare`.
Its sole postponed theorem is this node; every helper definition has actual data.
The statement is unchanged. Two existing definition nodes are added to `stmt_deps`:
`def-sp-open-scalar-tensor-data` and
`def-pur-integral-compact-support-coefficient-data`, whose declarations supply the
normalized representative presentations and the actual proper/open projection composite.
No new node or dependency repair is needed.

Hypotheses and clauses, with all helper names below in namespace
`WeilConjectures.ConcreteProjectionReduction`:

- The fixed finite-field datum is `D : FiniteFieldDatum`; its coefficient datum
  `C : D.CoefficientDatum` includes the prime `C.l` and `C.different : C.l ≠ D.p`.
  The finite extension is `E`, with `Field`, `Algebra (Padic C.l) E`, and
  `FiniteDimensional (Padic C.l) E`. The integer ring and uniformizer are the
  dependency's constructions inside `Padic.coefficientExtensionRing C.l E n`.
  `hn : 1 ≤ n`, `1 ≤ m`, and `hmn : m ≤ n` give precisely the positive quotient levels.
  `quotient C.l E hmn` is `Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)`;
  it is induced by identity on the integer ring, with its target coefficient action.
- The operation datum is `_operations : SixFunctorOperationDatum D C E n hn`.
  The statement never takes a six-functor package that assumes projection invertibility.
  The formulas are the existing actual operations, so the datum is not used to
  supply an arbitrary map or a projection-isomorphism hypothesis.
- `X Y : Over (Spec (CommRingCat.of D.k))` and
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` (and similarly for Y)
  mean finite-type k-schemes. The bundled `f : X ⟶ Y` is a k-morphism.
  Its three instances `IsSeparated f.left`, `LocallyOfFiniteType f.left`,
  `QuasiCompact f.left` give separated finite type. There is no separatedness
  instance on either structure morphism.
- `K,L` are objects of the ordinary intrinsic constant-ring pro-etale derived
  categories, with the recorded `finiteTorConstructible` predicates, exactly
  Dᵇ_ctf. Universes use schemes and coefficient fields in u, site objects in u+1,
  site morphisms in u, and intrinsic module sheaves in u+1.
- `m₀ : OpenScalarTensor.Models` and `choices₀ : Choices m₀` express the existing
  normalized tensor/scalar representative presentations, not extra geometric
  assumptions or arbitrary comparisons. The models retain the genuine derived
  functors, their universal counits, and K-flat representative computations;
  scalar tensorators carry their pure-tensor normalization. The theorem quantifies
  over every such presentation. Their existence is already the dependency
  `open_scalar_tensor_normalization`; no object is chosen from an unnormalized
  Nonempty assertion in this module.
- `scalar m₀ (quotient ...) W` is rho_W, with its canonical `scalarIso` to the
  published scalar extension. Thus its object values on K and L are K_m,L_m.
  `input m₀ A f K L` is H=K tensor Lf*L. The first conclusion quantifies over
  both given Tor intervals and states `finiteTorConstructible` for H and
  `HasProEtaleTorAmplitude ... H (a+c) (b+d)`. Orderedness is already a clause
  of each `HasProEtaleTorAmplitude`; no redundant ordering hypothesis is added.
- `support A cpt` is the dependency's `PurCompactSupport.image`, precisely
  derived proper image after exact extension by zero at the chosen compactification.
  `source` is S=Rf_!K tensor L; `target` is T=Rf_!(K tensor Lf*L).
  `projection` evaluates `PurCompactSupport.projectionMap`, which is defined by
  `SuppliedExchangeProjection.compactificationProjectionFromData`: the counit
  proper projection followed by the normalized open tensor comparison and the
  geometric pullback compositor. Its mu and gamma are characterized componentwise
  by the existing canonical representative comparisons; no freely supplied map
  replaces this composite. The constant-ring coefficient compositor is exactly
  `proEtaleConstantRingCompositeCoefficients_eq ... .symm`.
- `supportComparison` is the scalar-adjunction mate
  `PurCompactSupport.comparison (coefficientChange φ) cpt`, conjugated only by
  `scalarIso`. This is the universal scalar-unit/proper-open-restriction comparison,
  rather than an arbitrary isomorphism of its endpoints.
- `sourceComparison` is u: first `(choices.scalarTensor φ Y).iso.hom`, then
  the B tensor of `supportComparison ... K` and identity. `targetComparison` is v:
  first `supportComparison ... H`, then B compact support applied to
  `inputComparison`. The latter is the scalar tensor comparison followed by
  `(lambda ... f).symm` on L. These are precisely the two required orders.
- `Square` says both canonical arrows are `IsIso` and gives
  `rho.map PF_A ≫ v = u ≫ PF_B`. This is the displayed equation in diagrammatic
  order. It does not say `IsIso PF`.
- `Naturality` displays the source and target comparison squares for arbitrary
  maps in each input, and naturality of the actual PF composite. These equations
  are universal naturality of the same factors; invertibility is still restricted
  to the theorem's finite-Tor input pair.
- For `1 ≤ r ≤ m`, `Composition` gives the successive u and v equations.
  Each left side is scalar image of the first comparison, then the second
  comparison, then the source/target functor applied to the two input balanced
  associators. Each right side is the output balanced associator followed by
  the direct comparison for `ψ.comp φ`. For quotient maps this composite is the
  direct quotient map from n to r. `scalarComp` is the published unit-normalized
  balanced tensor associator, including the constant-ring composition transport.
- `Identity` gives u and v for the identity ring map, followed by the source/target
  functor applied to the two scalar unitors, equal to the scalar unitor at S,T.
  Since the level-n-to-level-n quotient is identity, this includes m=n.
- `cpt : Compactification f.left` is universally quantified, so every chosen
  compactification is covered. Its actual proper counit/open tensor composite
  remains present in each square and in the naturality equations.

Dependency declarations inspected and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: positive-level
  `Padic.finite_coefficientExtensionRing`, and the imported integer-ring,
  uniformizer, ideal and quotient constructions.
- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the compact-support convention
  without separated structure morphisms; the finite candidate itself is used
  through `PurCompactSupport.image`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: publicly reexports
  `WeilConjectures.finiteTorConstructible` and the intrinsic Tor predicates.
- `Sheaf.SixFunctors.OpenScalarTensorData`: `Models`, `Choices`, `scalar`,
  `scalarIso`, `tensor`, `tensorModel`, `lambda`, `scalarComp`, `scalarId`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`:
  `Coefficients`, `Change`, `image`, `comparison`, `projectionMap`, including
  its canonical `ProjectionComparisons` and open-factor normalizations.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`:
  `proEtaleConstantRingCompositeCoefficients_eq`.

All 13 recorded proof-dependency modules are imported with proof visibility unless
already public as statement data. Their recorded declarations were read, including
`sf_pullback_torAmplitude`, `finiteCoefficient_tensor_ctf`,
`compactSupportCoefficientComparisonPlus` and its isomorphism theorem,
`ringedTopoiCanonicalDerivedTensorPullback`,
`kflat_scalar_comparison_normalization`, `ringedExchangeTensorCoherence`,
`proEtaleScalarMateNormalization`, `open_scalar_tensor_normalization`,
`intrinsicCompactSupportCoefficientComparison`, `intrinsicCompactSupportRestriction`,
`successive_derived_quotient_normalization`, and `ringedCoefficientProjectionCocycle`.
The declaration docstring carries all six proof steps, including the explicit
proper/open factorization and the representative check for successive tensorators.

Edge cases checked against the definitions: m=n uses the scalar unitor rather than
requiring literal equality of chosen functors; r=m and r=m=n are retained; A₂→A₁
can be nonflat, with no flatness premise introduced; the zero inputs and empty
scheme/open are allowed; schemes with nonseparated structure morphisms are allowed.
The Tor predicates already require ordered intervals, and zero complexes may have
any such interval. No hypothesis that PF is invertible occurs anywhere.

Searches actually run:

- msearch.py leanfinder: “Canonical compact support projection map commutes with
  derived finite quotient coefficient reduction” returned eight unrelated
  Profinite.Nobeling projection/restriction results, not this derived square.
- msearch.py loogle: `CategoryTheory.Adjunction, "projection"` returned zero hits.
- msearch.py grep: `projection.*(reduc|coefficient)|reduc.*projection` returned
  nine Lean implementation/unrelated alternating-module hits.
- rg of both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream names index,
  for projection/reduction/coefficient terms found existing primitive comparison
  maps and the nearby `ProjectionReductionWitnessedFlatDomains`, which requires
  separated structure morphisms and states representative domains rather than
  this natural square/cocycle. The upstream `CoefficientReduction` is etale and
  does not identify this intrinsic proper/open composite on the stated domains.
  The existing actual operations and canonical normalizations are reused.
- The item-id search in project sources yielded no existing declaration for this node.

No statement dispute or source correction was found. Compiler and delivery validation
are performed with the prescribed scompile.py and deliver2.py wrappers.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
