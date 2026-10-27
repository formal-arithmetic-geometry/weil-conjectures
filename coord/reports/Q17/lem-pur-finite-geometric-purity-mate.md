## Worker report

The module `Sheaf.Paper.FiniteGeometricPurityMate` states the finite geometric
Frobenius purity/counit-mate assertion. No proof is supplied: each postponed
assertion has proof `by sorry`, its source, and its natural-language proof in its
own docstring. All definitions have actual data. The main declaration is
`WeilConjectures.PurityFiniteSetting.finiteGeometricPurityMate`; its companion
clauses and construction helpers are listed in `lean.declarations`.

Hypotheses and clause correspondence:

- The finite field, its fixed algebraic closure, the prime distinct from the
  characteristic, the finite extension of Q_ell, and the positive quotient level
  are exactly `P : PurityFiniteSetting.{u}`. `P.Ring` is the recorded
  `Padic.coefficientExtensionRing` quotient, not a power-of-ell reindexing.
  `P.Coefficient` is its existing ULift for small-site module values.
- `X₀ Y₀ : Over (Spec (.of P.field.k₀))` bind the two actual model schemes.
  The three instances `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on
  each `.hom` say separated finite type. The same three instances on `f₀.left`
  give the relative hypotheses. `P.frobeniusFiber` and `P.frobeniusMap f₀`
  are precisely the dependency's chosen geometric base changes.
- `d : ℕ` and `[SmoothOfRelativeDimension d (P.frobeniusMap f₀)]` give smooth
  pure relative dimension d, including zero. Derived categories use the actual
  `Scheme.ProEt.topology` and existing coefficient module category.
- The complex is `M` in the fixed-scalar presentation. `hM` states that its image
  under `Scheme.sfIntrinsicDerivedEquivalence.functor` belongs to the original
  `finiteTorConstructible` domain. This is an equivalence of the actual coefficient
  categories, so every intrinsic K is represented; this adds no etale-representative
  or flat-model hypothesis. `geometricPurityInput` asserts the same property for PK.
- P and Q of the mathematical statement are `P.smoothPurityPullback` at
  `P.frobeniusGaloisMap Y₀` and at `P.frobeniusGaloisMap X₀`, respectively.
  The letter P in Lean denotes the setting, not that pullback functor.
- H is `compositionTwistShift X d` after `smoothPurityPullback f`; it is the
  exact source of the recorded smooth purity map, with its recorded shifted Tate
  line and opposite-shift presentation. `geometricPurityMap` conjugates the
  recorded `existsUnique_smoothPurityTensorMap` composite by the two realization
  units. Both orientation and tensor transpose are retained. It is Gamma in
  fixed-scalar coordinates; `geometricPurityMapIsIso` records invertibility and
  `geometricPurityIso` uses precisely that arrow and its inverse.
- `geometricPurityCompactification` is the existing finite-type-over-field
  compactification, using the same proof instances as `smoothPurityExceptionalOver`.
  `geometricPurityF` is its actual proper/open compact-support functor. G is the
  dependency's `smoothPurityExceptionalOver`; `geometricPurityCounit` is the
  published `rightDerivedUpperShriekCounit`. The zero branch merely totalizes the
  existing bounded-below counit, just as in `SmoothTrace`; it is not used on any
  object quantified by this node.
- `geometricPurityB` is the published
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, surrounded by its
  exact-pullback comparisons and followed by the canonical compactification
  comparison on bounded-below etale-origin inputs. Thus the source is PFM and
  target FQM for the same retained compactification. This handles the change of
  compactification explicitly, without postulating an ambient pro-etale adjoint
  or an ambient compactification-independence theorem. `geometricPurityBIsIso`
  states invertibility for every bounded constructible finite-Tor M. The main
  theorem additionally spells it out at G K.
- `geometricPurityGamma` is the exact geometric field Frobenius used in
  `frobeniusGaloisMap`. `geometricPurityRetag` is `Over.map (Spec.map gamma)`;
  its underlying scheme is unchanged. `geometricPurityRetagProperties` states
  unchanged underlying object, separated finite type, and the structure-map
  equation making g_T a k-morphism. `geometricPurityRetagMap` is the retagged
  f, as the actual map of `Over.map`; `geometricPurityRetagFrobenius` is the
  actual g_T bundled over k.
- `geometricPurityRetagging` states the Cartesian square, equality of the retained
  compactifications, and equality of diagonal orientations, tensor-map transposes
  in every etale presentation, and exceptional counits. `HEq` is used only for
  the two structure-map presentations of the same underlying categories. The
  counit-preserving right-adjoint identification is the identity under these
  chosen coordinates, so these equalities include that transport.
- `geometricPuritySourceInChart` constructs the actual pullback/shift/source map
  using the already normalized root charts. Its source chart uses zeta; its
  target chart uses **gamma(zeta)**, not zeta. This is essential for semilinear
  geometric Frobenius. The middle factor is the canonical pullback compositor
  and the exact square equality. The root-chart normalization is on actual roots
  of unity, and so fixes tau_d without an extra scalar. The d=0 chart is the
  coefficient unit. `existsUnique_geometricPuritySource` fixes the map in every
  such root chart, so `geometricPuritySource` chooses only a uniquely specified
  isomorphism. It never uses purity, its inverse, or the exceptional mate to
  define b. This construction is equivalent to the roots inverse-image comparison
  in `FrobeniusCoefficientTwistsCanonical`: on a constant root it applies gamma,
  then scalar extension, reduction and ordered tensor powers.
- `existsUnique_geometricPurityMate` states the exact counit equation
  `B_(G K) ≫ F.map e ≫ epsilon_(P K) = P.map epsilon_K`.
  Since the first factor is invertible, the standing Hom bijection identifies it
  with precisely the transpose of `B_(G K)^-1 ≫ P.map epsilon_K`.
  `geometricPurityMate` extracts this uniquely fixed arrow, independently of
  purity. It is also finite exceptional base change for the retagged square:
  that map is defined by the same compact-support word and counit transpose,
  and `geometricPurityRetagging` identifies both. There is no arbitrary map or
  stronger adjunction hypothesis.
- `finiteGeometricPurityMate` states the commuting purity square in Lean's
  left-to-right composition order, and then the literal formula using the inverse
  of Q Gamma. The identical `geometricPuritySource` occurs in both formulas.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient` and the finite-field/coefficient data.
- Mathlib `AlgebraicGeometry.Morphisms.Smooth`, `FiniteType`, and `Proper`:
  `SmoothOfRelativeDimension`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`. Finite type is the conjunction of locally finite type and
  quasi-compactness, not an extra class.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`: `frobeniusFiber`,
  `frobeniusMap`, `frobeniusGaloisMap`.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian`.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityPullback`,
  `smoothPurityExceptionalOver`, `smoothPurityReassociation`,
  `smoothPurityTensorMapInPresentation`, `existsUnique_smoothPurityTensorMap`;
  `PurityDiagonalDualizingObject.diagonalDualizingObject` through that import.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  `ConstructibleExceptionalCoefficients.System` supplies the constructible scope;
  its underlying finite functor is used through `smoothPurityExceptionalOver`.
  The actual counit is the published finite-coefficient
  `ProEtale.rightDerivedUpperShriekCounit`, never a full ambient adjunction.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains` supplies the recorded generic
  exchange notion. Its concrete proper/open word here is the published
  `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `rightDerivedLowerShriekOfCompactificationEtaleOriginIso`.
- `Sheaf.Paper.PurityCompositionCoherence`:
  `compositionTwistShift`, `compositionFixedPullbackComp` via the recorded
  `def-pur-composition-comparisons` interface.
- `Sheaf.Paper.FiniteReductionRootCharts`: `finiteReductionFixedChart`, using
  the uniquely section-normalized root-line charts and ordered tensor powers.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`: normalized finite positive
  and signed line maps; its roots-of-unity normalization is rendered by the
  gamma(zeta) target chart, with no additional generator choice.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`.

The four added statement dependencies already exist with Lean records:
`def-pur-finite-reduction-root-charts`, `def-pur-composition-comparisons`,
`lem-weil-frobenius-square-cartesian`, and `def-weil-finite-tor-amplitude`.
They name the interfaces used in the signatures. No new node, dependency repair,
or change to the mathematical statement is needed.

Edge cases checked against the source and formulas: d=0 retains the unit/root-zero
normalization; f=id and the identity square use the same compositors; M=0 and empty
schemes introduce no nonemptiness condition; n=1 remains a positive quotient;
ramified E uses the actual uniformizer quotient and not an unramified identification;
no assertion of arbitrary unbounded compactification independence or ambient
pro-etale adjunction is made. All universes and variables are explicitly bound.

Searches: the prescribed msearch LeanFinder query was “Finite coefficient smooth
purity under geometric Frobenius is the counit mate of compact support base change”
(8 unrelated algebra/module-adjunction hits); Loogle queried
`CategoryTheory.Adjunction.homEquiv, CategoryTheory.mateEquiv` (0 hits); Mathlib grep
queried `smoothPurity|geometric.*[Pp]urity|semilinear.*purity` (0 hits). The wrapper
records are retained in `searches.jsonl`. Direct rg through `lean/WeilConjectures`
and `lean/Sheaf` for this node id and geometric-purity names found no existing
statement. Further source searches located the exact compactification comparison,
finite counit, purity map and root charts used above. No Mathlib or project
declaration states the full item already.

The current blueprint equivariance proof and the current finite base-change factors
were read under `literature/blueprint/latest/`. No STATEMENT-DISPUTED issue was found.
Compilation uses only the prescribed scompile wrapper; both sandbox and normal
module-mode library checks pass on the server.

## Second reading by Q17

The dispatcher explicitly forbids starting another agent and states that the
maintainer supplies the independent review. Accordingly this section records my
own second clause-by-clause reading, not a claim of an independent reviewer.
The main potential mismatches checked were the fixed-scalar versus intrinsic
coefficient presentation, the scope of the exceptional adjunction, compactification
transport at the exchange target, and the semilinear target root. The module keeps
both realization units, uses only the relative counit, explicitly includes the
canonical compactification comparison, and uses gamma(zeta). The retagging
orientation and tensor transpose are separate assertions. Every postponed theorem
belongs to a clause of the owning node and has its complete proof plan. No clause
or hypothesis of the node is discarded, and no arbitrary map replaces a canonical
construction.
