## Worker report

The module `Sheaf.Paper.FiniteMateDomain` states
`WeilConjectures.FiniteMateDomain.finiteMateDomain`, with its sole proof `by sorry`.
Its six transparent abbreviations name the existing coefficient ring, etale mate,
ambient pro-etale mate, comparison inverse image, and source/target comparison
isomorphisms. They contain real data and introduce no independent construction.
No node statement or dependency changes, no new nodes, and no dependency repairs.

The previous BLOCKED result conflated the stages. Q91's 09:49 merge completed the
stage-1 split, with an unchanged statement; the live node has no Lean record.
It does not supersede this stage-2 task. This delivery uses Q91's full accepted
five-step proof plan, including the reviewer's smooth-arrow identification fix.

Hypothesis and clause correspondence:

- The finite-field datum `(p,a,q,k0,k)` is `D : FiniteFieldDatum.{u}` (the explicitly
  bound section parameter). `C : D.CoefficientDatum` supplies a prime `C.l`, the
  condition `C.l ≠ D.p`, and the fixed algebraic closure of the coefficient field.
  `E : Type u`, `Field E`, `Algebra (Padic C.l) E`, and
  `FiniteDimensional (Padic C.l) E` are the arbitrary finite extension. No norm,
  topology, uniformizer, coefficient finiteness, or annihilator is an extra hypothesis.
- `n : ℕ` and `hn : 1 ≤ n` give exactly the positive quotient level.
  `Coefficient C E n` is `ULift.{u+1} (Padic.coefficientExtensionRing C.l E n)`.
  The latter is the existing quotient of the spectral-norm integer ring by the
  nth power of its chosen uniformizer ideal. The lift is the established module
  universe convention of `SixFunctorOperationDatum.finiteExchangeProjection`;
  it changes no ring operations or module contents.
- `X X' Y Y' : SixFunctorSpace D` are finite-type k-schemes: their underlying
  over-objects have locally finite type and quasi-compact structure maps.
  Each of the four explicit `IsSeparated ...obj.hom` instances gives the scheme
  separatedness. The four morphisms are morphisms in that full over-category,
  so all are k-morphisms. For each underlying scheme morphism, its explicit
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances render
  separated finite type. Neither smoothness nor properness of any other arrow
  is silently inferred as an assumption.
- `sq : ChosenCartesianSquare g'.hom.left f'.hom.left f.hom.left g.hom.left`
  retains the chosen fibre-product identification and its two projection
  equations. `hgeom : IsProper f.hom.left ∨ Smooth g.hom.left` is exactly the
  proper-or-smooth hypothesis, with the original arrow roles.
- The first universal quantifier ranges over all `L : DerivedCategory.Plus`
  of etale `ModuleCat` sheaves. Its `IsIso ((etaleMate ...).app L)` is the
  constant-module assertion on D+, without constructibility or finite Tor.
- The next equality applies the canonical derived `moduleAbelianForget` to
  that very mate, then `moduleAbelianDerivedExchangeTargetIso`, and equates
  this to `moduleAbelianDerivedExchangeSourceIso` followed by the abelian
  `derivedBaseChangeMapPlus` at the forgotten L. These are the canonical
  coefficient comparisons, not existential endpoint isomorphisms. Combined
  with the preceding IsIso, it asserts abelian exchange is invertible too.
  The torsion/allowable-torsion condition follows from the actual coefficient
  quotient and is not added as an assumption.
- The third conjunct of the first universal assertion is literally the
  displayed site equation: `comparison.map (Plus.ι.map E_L) ≫ T_L.hom =
  S_L.hom ≫ ambientMate.app (comparison.obj L.obj)`. With Lean's composition
  order this is `T_L ν*(E_L) = Ex_*(ν*L) S_L`. `sourceIso` and `targetIso`
  alias `baseChangeSourceComparisonIso` and `baseChangeTargetComparisonIso`,
  so they have the two exact displayed source/target types in the node.
  The explicit finite-type/separated assumptions supply their qcqs instances.
- The second universal assertion ranges over every `K : DerivedCategory.Plus`
  of pro-etale module sheaves and every supplied
  `W : FixedEtaleOriginWitness ... K`. Its fields `W.complex` and `W.iso`
  retain the antecedent and the original isomorphism `ν*L ≅ K` as data.
- Its premise is `IsProper f ∨ (Smooth g ∧ boundedConstructible W.complex.obj)`.
  The proper case permits every D+ antecedent. The smooth case requires the
  actual retained antecedent to be bounded constructible. In particular there
  is no restriction to a chosen antecedent selected from an existence proof.
- The conclusion gives `IsIso ((ambientMate ...).app K.obj)` and the explicit
  five-factor conjugation, in Lean order:
  `P.map W.iso.inv ≫ S_L.inv ≫ ν*(E_L) ≫ T_L.hom ≫ Q.map W.iso.hom`.
  This is exactly `Q(alpha) T_L ν*(E_L) S_L^{-1} P(alpha)^{-1}`.
  It quantifies over every witness, not just the identity one.
- These ambient endpoints are `P(K.obj)` and `Q(K.obj)` in the ordinary
  unbounded derived category. No bounded-constructible landing conclusion is
  added. Bounded constructible finite-Tor inputs are included by the same
  universal statement; no finite-Tor assumption limits either displayed domain.
- The smooth role tuple is `(g,f,f',g')`, as recorded in the proof docstring;
  both exchange maps land at Y'. This sentence describes the indexing of the
  cited theorem, not an additional hypothesis or structure to formalize.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum` and `.finiteExchangeProjection`;
  `SixFunctorSpace` is reexported from `SixFunctorOperationDatumStages`.
  In particular the finite actual operation uses exactly the fixed-scalar
  `ProEtale.derivedBaseChangeMap` appearing here. The datum supplies notation
  and constructions; its unrelated exceptional/compact-support/higher-stage
  structure is not an additional hypothesis of ordinary finite exchange.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`, `hom_fst`,
  `hom_snd`, and inherited `toCommSq`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.exchange`
  (the supplied-domain mate recipe). Its finite specialization is the published
  `AlgebraicGeometry.ProEtale.derivedBaseChangeMap` from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`.
  I read its full definition: it is `mateEquiv` of the derived adjunctions and
  `leftDerivedUpperStarSquareIso`, built from pullback composition and sq.w.
  This is the ambient constant-module ringed mate in its fixed-scalar
  presentation, exactly as used by the existing finite operation datum; no
  arbitrary map or supplied exchange-stage data replace it.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, `complex`, and `iso`.
  This recorded interface explicitly provides fixed-scalar coordinates. Its
  ringed-interface predecessor remains publicly reexported and is not replaced.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`:
  `comparison_derivedBaseChangeMap`, `baseChangeSourceComparisonIso`, and
  `baseChangeTargetComparisonIso` in `AlgebraicGeometry.ProEtale`; their full
  signatures and construction docstrings were read. `comparisonUpperStar`
  is the existing exact comparison functor, not a new construction.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`:
  `AlgebraicGeometry.Etale.exchange_forget_coefficients`, with the canonical
  source/target isomorphisms reexported from
  `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility`.
- The plain proof imports retain all stated proof dependencies: spectral-norm
  absolute value (Mathlib.Analysis.Normed.Unbundled.SpectralNorm),
  `Padic.extension_integers_dvr` (Sheaf.NumberTheory.Padics.ExtensionIntegersDvr),
  finite valued-DVR quotients (Mathlib.Topology.Algebra.Valued.LocallyCompact),
  locally finite type/quasi-compactness (Mathlib.AlgebraicGeometry.Morphisms.FiniteType),
  separated implies quasi-separated (Morphisms.Separated), qcqs/finite-presentation
  base-change permanence (Morphisms.QuasiSeparated and Morphisms.FinitePresentation),
  `Etale.isIso_baseChange_of_isProper` (WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper),
  `Etale.boundedBelow_derived_smooth_baseChange`
  (Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange),
  `Etale.abelianDerivedBaseChangeArrow`
  (Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets), and
  `Etale.derivedBaseChangeMapPlus` (WeilConjectures.SixFunctors.BaseChange.Derived).

Edge cases checked before writing: zero objects and empty schemes impose no
nonemptiness restrictions; identity and arbitrary finite-type horizontal maps
are retained in the proper case; both alternatives may hold at once; in the
smooth case the only extra condition is on the retained etale antecedent;
identity witnesses and arbitrary nonidentity witnesses have the same correctly
oriented conjugation; n=1 is included, n=0 is excluded exactly by the source.
There is one explicit universe u: the small sites retain object universe u+1
and morphism universe u, and coefficients/modules use the standard u+1 lift.
No equality between those site universes or coefficient-smallness assumption is
introduced. `autoImplicit` and `relaxedAutoImplicit` are both disabled.

Searches actually run for this delivery:

- msearch.py, leanfinder: “Proper or smooth base change for finite torsion etale
  complexes with etale proetale comparison of the adjunction mate exchange”.
  Eight results: etale base-change stability, etale composition, and Kahler
  differential base change; none states the combined assertion.
- msearch.py, loogle: `CategoryTheory.Adjunction, CategoryTheory.IsPullback`.
  Successful query, zero hits.
- msearch.py, grep: `proper.*base.?change|smooth.*base.?change|etale.*exchange`.
  Twenty-five hits, on ring-under properties, regular categories, morphism
  properties, and scheme morphism stability; none matches this assertion.
- msearch.py, leansearch: “Finite ordinary etale base change and its proetale
  site comparison for actual mates”. Eight hits, on etale/finite stability,
  IsBaseChange, the monoidal Frobenius mate, and the etale topology; none matches.
- rg in lean/WeilConjectures and lean/Sheaf for the exact node id returned no
  existing module; searches for comparison_derivedBaseChangeMap and the finite
  exchange/ambient-ringed names found the components cited above, including the
  explicit finite exchange definition in ExchangeProjection.lean. Searches for
  finiteMateDomain and its namespace found no name collision.

The theorem is an assembly of existing components, not a duplicate of one
existing declaration: coefficient forgetting, the proper-or-smooth D+ etale
assertion, site comparison, and arbitrary retained-witness conjugation are
combined here with exactly the stated geometric/coefficient domain.
No STATEMENT-DISPUTED issue or statement correction was found.

Validation: scompile.py compiled this file in both sandbox and library module
contexts against the published server build, without errors or warnings
(19.2 s and 21.6 s respectively). No global build or direct repository write.
The required deliver2.py dry run and push follow this report.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
