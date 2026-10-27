## Worker report

The module `Sheaf.Paper.ProjectionReductionWitnessedFlatDomains` states
`WeilConjectures.ProjectionReduction.exists_witnessedFlatDomains`. Its only postponed
proof is `sorry`. The other declarations are real constructions or transparent clause
packages belonging to this node. No source statement is changed and no dependency is
redefined. In particular no six-functor projection-formula axiom is assumed.

Hypotheses and clauses, in statement order:

- `D : FiniteFieldDatum` retains p,a,q,k_0 and the fixed algebraic closure k.
  `C : D.CoefficientDatum` supplies the prime ell and `C.different : C.l ≠ D.p`.
  E has `Field`, `Algebra (Padic C.l) E`, and `FiniteDimensional` instances.
  `Coeff C.l E n` is exactly the canonical ULift of the recorded quotient
  `Padic.coefficientExtensionRing C.l E n`, with its recorded valuation ring and
  uniformizer. `m,n`, the two positive-level `Fact` instances, and `hmn` render
  1 ≤ m ≤ n. `quotient` is `Ideal.Quotient.factor` for the inclusion of powers,
  followed by `.ulift`. It is not an arbitrary ring homomorphism.
- X and Y are schemes in an arbitrary universe u with structure maps to Spec D.k.
  `LocallyOfFiniteType` plus `QuasiCompact` renders finite type; `IsSeparated`
  on both structure maps renders separatedness over k. The identical three
  properties on f and `f.IsOver` render a separated finite-type k-morphism.
- The ambient `ProDerived` is the ordinary fixed-ring module-sheaf derived
  category on the actual small pro-etale site. Its object universe is u+1 and
  site morphism universe u, with coefficient modules in u+1. It does not replace
  the small site by a larger site or equate its two universes.
- `_hK,_hL` use the recorded native `constructibleFiniteTor` predicate.
  `_hKTor,_hLTor` use the full `torAmplitudeIn` tests on all pro-etale module
  sheaves, with the explicitly ordered integer intervals `[a,b]` and `[c,d]`.
- `∃ P,Q` chooses actual cochain complexes on the small etale sites. In `stage`,
  the two `model` clauses assert exactness of tensorRight for every term, finite
  constant-value constructibility using `IsConstructibleEtaleModuleSheaf`, and
  `IsZero` for all terms strictly outside the prescribed closed intervals.
  On the Noetherian schemes in this statement, the locally closed strata in the
  recorded constructibility predicate are constructible subsets.
- `origin` applies the exact comparison's `mapDerivedCategory` to `Q.obj P`.
  The two `Nonempty` isomorphism clauses are exactly the chosen etale-origin
  witnesses for K and L, rather than equalities of objects or mere membership
  with no specified source object.
- The first `stage` is the A stage, with P_A=P and Q_A=Q. The second uses
  `reduceComplex quotient X P` and its Y analogue, the actual termwise scalar
  extension functors. K_B and L_B use the actual `proFixedScalar` derived
  scalar extension, retaining B-actions; there is no flatness assumption on B/A.
  Both stages therefore use reductions of the SAME P,Q.
- `total` is `CochainComplex.mapBifunctor` for P_R and the exact termwise
  etale inverse image of Q_R using the published sheaf tensor structure. This
  is the signed total tensor, not an arbitrary complex with matching cohomology.
  Its `model` clause gives flat constructible terms and strict support in
  `[a+c,b+d]`. Its `origin` isomorphism has target `tensorInput`, exactly
  K_R tensor^L Lf_R^* L_R, using the published derived tensor and left-derived
  upperStar.
- The three `witnessedDomain` clauses assert membership in the actual finite-Tor
  constructible category and the full specified Tor interval for K_R,L_R,H_R.
  They also exhibit a bounded finite-value-constructible etale object and an
  isomorphism of its comparison image with each pro-etale object.
- `Nonempty (Compactification f)` asserts compactification existence. The final
  universal binder of EACH stage ranges over EVERY `Compactification f`, whose
  fields supply j open, r proper, and rj=f. Its two `witnessedDomain` conclusions
  give bounded constructible etale origins and precisely `[a,b]` and
  `[a+c,b+d]` for j_!K_R and j_!H_R. The open extension is the published exact
  openImmersionLowerShriek.mapDerivedCategory.
- The final canonical-isomorphism clause is delivered as the explicit definition
  `openTensorIso`, with exactly source j_!H_R and target j_!K_R tensor^L Lr_R^*L_R.
  Its body applies the recorded pullback congruence for `comp.comm`, the
  recorded composition isomorphism, and the recorded open projection ISO in
  its j_!(tensor) -> tensor(j_!) direction. This is a real construction for every
  compactification and both coefficient rings; no arbitrary isomorphism choice
  or additional theorem is used. Thus the identified proper-factor tensor has
  the second input's witnessed domain.

Recorded statement dependencies used:

- `Sheaf.Paper.SixFunctorDatum`: imports the existing `FiniteFieldDatum` and
  its `CoefficientDatum`; the axiom structure `SixFunctorDatum` itself is not
  assumed, since the result verifies concrete finite-coefficient domains.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the existing ordinary module
  realization and comparison convention; fixed ModuleCat presentation is used
  consistently with `ComparisonDerivedPullbackFixed` and the native Tor predicate.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and ordinary localization/cohomology convention.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  its underlying `ProEtale.comparisonUpperStar.mapDerivedCategory`, the same
  exact termwise comparison whose bounded-below restriction it records.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: publicly exposes the recorded native
  `ProEtale.DerivedCategory.constructibleFiniteTor` and `torAmplitudeIn` used here.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`,
  including its open/proper fields and factorization equality.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`:
  `derivedOpenImmersionLowerShriekProjectionIso`, used in `openTensorIso`.

The recorded proof dependency modules are imported, with proof-only imports plain
and modules whose operations occur in helper signatures public. The published
`FlatModuleCat.upperStarPreservesFlat_moduleCat` instance supplies the canonical
flat-pullback instance for finite (hence Noetherian) coefficient rings. The native
pullback composition is supplied by the standard upstream interface, avoiding
parallel copies. No dependency repair was necessary.

Edge cases checked mathematically: m=n gives the identity quotient; m=n=1 is
allowed. Empty X or Y is permitted, as are K=0 or L=0, singleton intervals,
negative endpoints, identity f, and every compactification including identity or
empty-source j. The full Tor tests are retained. A nonflat quotient such as
Z/4 -> F_2 is allowed: a bounded flat input, not a flat quotient, computes its
reduction. Finite-type hypotheses imply Noetherianity; ell ≠ p makes ell a unit
on X,Y and each compactification source. Universe u is arbitrary and no test
sheaf is confined to etale origin. No disputed statement or node fault found.

Searches for an existing statement (all run through msearch.py):

- LeanFinder: "Bounded constructible complexes of finite Tor amplitude admit
  bounded flat constructible etale models compatible with coefficient reduction
  pullback tensor and extension by zero." Eight results, ordinary etale-algebra
  base-change and finite-presentation results; no match for this statement.
- Loogle: `"Constructible", "Flat"`. Zero hits.
- Mathlib grep: `constructible.*flat|flat.*constructible|witnessedFlatDomains`.
  Zero hits.
- Project rg in WeilConjectures and Sheaf:
  `witnessedFlatDomains|witnessed.*[Ff]lat|reduction.*[Dd]omain`. No simultaneous
  statement; matches were unrelated ring-domain results and the different
  `FiniteCompactSupportDomains` compact-support-output lemma. An exact item-id
  search in WeilConjectures had no result. Helper constructions use the existing
  scalar, tensor, inverse-image and comparison operations rather than copies.

Validation: the complete module compiled through the prescribed scompile.py
server wrapper. The delivery dry run and final delivery are recorded by the wrapper.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
