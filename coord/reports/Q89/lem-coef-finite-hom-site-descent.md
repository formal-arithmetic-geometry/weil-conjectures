## Worker report

The module `Sheaf.Paper.CoefFiniteHomSiteDescent` states
`WeilConjectures.coefFiniteHomSiteDescent`, with proof `sorry`. Its other declarations
are fully defined clause assemblers and canonical isomorphisms belonging to this
node, all listed in `lean.declarations`. No definition contains postponed data or
an unnamed proof. No natural-language statement correction is needed.

The source read is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.proof.md`,
especially its final paragraph and final site-comparison sentence, together with
all seven expanded proof steps of the assigned node. The theorem docstring gives
those seven steps, including the local tensor calculation and the inverse in the
first Hom input. The parent coefficient-Hom isomorphism theorem is not used.

Hypotheses and ambient objects:

- `D : FiniteFieldDatum.{u}` supplies the fixed algebraic closure of the finite
  field, its characteristic prime, and the cardinality convention. `l : ℕ`,
  `[Fact l.Prime]` and `_hl : l ≠ D.p` render precisely the coefficient-prime
  hypotheses. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` render the finite extension. Its valuation ring,
  uniformizer-independent power ideals and quotients are the existing Padic
  coefficient constructions, rather than additional parameters.
- `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`, and the separated, locally of
  finite type and quasi-compact instances on `X ↘ Spec (.of D.k)` say exactly
  separated finite type over the fixed field. There is no smoothness, properness,
  nonemptiness or flatness assumption.
- Every positive exponent is represented by `n + 1`. Thus `n m : ℕ` and
  `h : m ≤ n` are exactly the node's positive levels `n ≥ m ≥ 1`; `r : ℕ` and
  `k : r ≤ m` cover all further positive quotients. The coefficient map is
  `finiteHomQuotient`, the actual quotient factor homomorphism.
- The etale category is `finiteHomEtale`, the recorded
  `Etale.DerivedCategoryModule` with its canonical `ULift` coefficient ring.
  The intrinsic pro-etale category is `normalizedDVRDerived`, over the existing
  constant ring sheaf. The latter retains site object universe `u+1`, morphism
  universe `u`, module universe `u+1` and standard derived localization universe
  `u+2`. It is not replaced by the etale derived category or a completed category.
- `finiteHomEtaleClosed` and `finiteIntrinsicClosed` supply the published ordinary
  uncompleted derived tensors and internal Homs. `finiteTorConstructibleEtale`
  and `finiteTorConstructible` are the recorded bounded constructible finite-Tor
  predicates. Their amplitude predicates test every degree-zero module sheaf;
  neither perfect complexes nor locally free tests replace them.
- `finiteHomNuOrdinary` and `finiteHomNu` are the published ordinary and exact
  derived inverse images for the actual site morphism.
  `finiteHomEtaleReduction` and `coefficientFiniteQuotientDerived` are the actual
  derived scalar extensions along the quotient. All maps below are morphisms in
  the appropriate coefficient-module derived category, so in particular the
  scalar/site isomorphism has B-linear components.

Clause correspondence:

1. `CoefFiniteHomDescent n`, asserted for every positive level, first records
   `PreservesFiniteLimits` and `PreservesFiniteColimits` for the ordinary additive
   comparison. Its next clause gives, for each intrinsic finite-Tor constructible
   `P`, an etale finite-Tor constructible `P'` and `Nonempty (U.obj P' ≅ P)`.
   The following clause quantifies over **every** bounded constructible etale
   witness and its isomorphism to `P`. For all integers `a ≤ b` it gives the
   equivalence of the etale and pro-etale Tor-amplitude predicates, retaining the
   specified interval rather than merely some finite amplitude. The last clause
   preserves the finite-Tor constructible category and each ordered Tor interval.
   The auxiliary `coefFiniteHomEtaleConstructible` is just the recorded etale
   bounded constructibility predicate with positive-level finiteness supplied.
2. `coefFiniteHomSiteIso h` is a natural isomorphism
   `F_et ⋙ U_B ≅ U_A ⋙ F_pro`, i.e. the stated objectwise direction. Its body is
   `(asIso (finiteHomSiteBeta ... h)).symm`, not a choice of objectwise
   isomorphisms. That published beta is the adjunction mate of
   `finiteHomNuDerivedRestriction`, itself exact descent of the unique ordinary
   restriction comparison fixed on every local generator by
   `FiniteHomNuRestrictionNormalization`. Thus this definition specifies the
   tensor identification on K-flat models: the inverse image of `x ⊗ b` maps
   to the inverse image of `x` tensor `b`. The existing normalization and mate
   determine this map; the statement does not parameterize an arbitrary h.
3. `CoefFiniteHomStrong` fixes the tensorator of a `Functor.CoreMonoidal` to the
   published comparison. The core structure includes associativity and both
   unit axioms. Its unit is determined by that tensorator and the unit axioms.
   `CoefFiniteHomMonoidalSquare` asks for these structures on all four functors
   and writes both the tensor square and its unit equation. The theorem supplies
   symmetry structures with the etale components fixed by `finiteHomKoszulIso`
   and the intrinsic components fixed by `RingedDerivedTensorCoherence` on the
   existing `finiteIntrinsicTensorModels`. `CoefFiniteHomSymmetry` writes the
   compatibility equation for the three families of tensorators. Hence neither
   the ambient symmetry nor the pullback tensor comparison is arbitrary.
   `CoefFiniteHomQuotientCoherence` explicitly writes the two routes for every
   `A → B → C`, using `finiteHomEtaleAssoc` and `finiteHomIntrinsicAssoc`.
   These are the published scalar associators (mates of identity-on-sections
   scalar-restriction reassociation). Identity levels remain included.
4. `CoefFiniteHomSquare` quantifies over etale finite-Tor constructible `K,M`.
   Its first two conjuncts assert `IsIso` of the specified site Hom comparison
   at A and at B on the reductions. `finiteHomSiteHom` is exactly the closed
   transpose of inverse image of evaluation under `finiteHomNuTensor`, whose
   K-flat normalization is prescribed by the existing site-Hom definition node.
5. The last conjunct of `CoefFiniteHomSquare` is the node's displayed equality,
   with composition read left to right in Lean:
   `h_H ≫ F_pro.map beta_A ≫ v_pro = U_B.map v_et ≫ beta_B ≫ H.map (...)`.
   Its first Hom component is `(h.inv.app K).op` and its second is
   `h.hom.app M`. Both sides therefore have the stated common source and target.
   `etaleFiniteHomCanonical` and `proEtaleFiniteHomCanonical` are the existing
   reduced-evaluation transposes. No scalar-Hom isomorphism is assumed or asserted.
6. `CoefFiniteHomLawsOn` writes naturality in both variables, preservation of
   arbitrary tensor-Hom transposes and internal-Hom composition. The transpose
   equation includes evaluation by taking its input to be evaluation (the
   transpose of evaluation is the identity). The test object `T` in this equation
   is unrestricted. The theorem transports these etale equations to the intrinsic
   equations on **every** intrinsic finite-Tor constructible pair, without a
   witness parameter or a choice-dependent arrow.
   `CoefFiniteHomSuccessive` transports the successive-quotient and identity
   equations: its premise is the conjunction of those equations for the etale
   finite-Tor constructible pairs, and its conclusion is their intrinsic analogue
   on every pro-etale finite-Tor constructible pair. Both successive equations
   use the canonical scalar associators and the inverse in the first Hom argument. `coefFiniteHomProUnit` is the
   canonical left-adjoint identity comparison obtained from `normalizedDVRResUnit`;
   it does not choose an arbitrary automorphism. These equations concern the
   canonical intrinsic maps and do not assert invertibility of v.

Dependency declarations used (names below are in `WeilConjectures` unless qualified):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the existing
  `Padic.coefficientExtensionRing` constructions it imports.
- The convention-only `def-weil-scheme-morphism-properties` is used through
  Mathlib's `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the ordinary module-derived
  category specified by that record); no torsion restriction is added.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its recorded existence
  interface, used by the existing intrinsic coefficient calculus.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, used through the intrinsic
  closed record; the etale Hom is the recorded `Etale.derivedHom`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`:
  `Etale.DerivedCategory.hasTorAmplitudeIn` (built from the recorded GE/LE tests).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `finiteIntrinsicTensorModels`, `coefficientFiniteInternalHom`,
  `coefficientFiniteQuotientDerived`, `coefficientDerivedSystemEvaluationCalculus`,
  and `finiteIntrinsicReductionHom`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, used by `finiteTorConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale` and the
  imported `finiteTorConstructible`, `HasProEtaleTorAmplitude`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  used through the recorded exact comparison functor rather than copied.
- `Sheaf.Paper.EtaleFiniteCoefficientHomArrow`: `finiteHomEtale`,
  `finiteHomQuotient`, `finiteHomEtaleClosed`, `finiteHomEtaleInternalHom`,
  `finiteHomEtaleReduction`, `finiteHomEtaleTensor`, `finiteHomKoszulIso`,
  `etaleFiniteHomCanonical`, `proEtaleFiniteHomCanonical`,
  `finiteHomEtaleAssoc` and `finiteHomIntrinsicAssoc`.
- `Sheaf.Paper.FiniteCoefficientSiteScalarArrow`: `finiteHomNuOrdinary`,
  `finiteHomNu`, `finiteHomSiteBeta`, including its existing invertibility instance
  and the local-generator normalization of its restriction mate.
- `Sheaf.Paper.FiniteCoefficientSiteChainTensor`: the existing ordinary signed
  total tensor comparison and localization factors used by the site tensorator.
- `Sheaf.Paper.FiniteCoefficientSiteHomArrow`: `finiteHomSiteHom`,
  `finiteHomNuTensor` and its existing representative normalization.
- `Sheaf.Paper.NormalizedOriginScalarComparisons`:
  `AlgebraicGeometry.ProEtale.normalizedOriginScalarUnit`, used directly for the
  etale identity equation in the transport premise. Its quotient-factor equality
  is `congrArg RingHom.ulift (Ideal.Quotient.factor_eq ...)`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedDerivedTensorCoherence`, used to specify the intrinsic symmetry.
  `NormalizedDVRTower` supplies the canonical `normalizedDVRResUnit` through the
  existing coefficient imports. Mathlib supplies `Functor.CoreMonoidal`,
  `Adjunction.leftAdjointIdIso`, opposite/product functors and natural isomorphisms.

The four already-landed finite-Hom definition node IDs and the landed
`def-weil-pbc-normalized-origin-scalar-comparisons` are appended to `stmt_deps`
to name the canonical interfaces actually used. Their statements, signatures and
normalizations were read. No dependency record is changed, no new DAG node is
needed, and no private substitute for a dependency is introduced. Proof-only
imports match the node's recorded seven-step argument; the two proof nodes with
no recorded Lean module are cited in the theorem's proof docstring, not silently
assumed as extra hypotheses.

Edge cases checked: exponent one is index zero; `n=m`, `r=m`, `r=n=m` and
nonadjacent quotients are allowed; both the zero complex and empty scheme remain
allowed; a quotient such as exponent two to one need not be flat, and every scalar
extension here is derived. The interval clauses quantify over all ordered integer
intervals (including singleton and negative-degree intervals), all degree-zero
module sheaf tests, and every bounded constructible witness. Tensor-Hom transposes
allow arbitrary test objects. Universe lifts do not force object and morphism
universes of the small pro-etale site to agree. The square contains the required
inverse precisely in its contravariant argument. None of these clauses uses
invertibility of v. No disputed statement was found.

Searches for reuse:

- `msearch.py ... leanfinder "Constructible finite Tor pro etale etale descent derived scalar extension internal Hom square"`:
  eight hits about algebraic etaleness, including `Algebra.Etale.comp` and
  `Algebra.FormallyEtale.of_restrictScalars`; none states this derived site square.
- `msearch.py ... loogle '"proetale", "Hom"'`: zero hits.
- `msearch.py ... grep '[Pp]ro[Ee]tale.*[Hh]om|[Ss]ite.*[Ss]calar'`:
  seven unrelated scalar/analytic/ring-theoretic hits; no matching theorem.
- `msearch.py ... leansearch "Etale proetale derived scalar extension internal Hom comparison"`:
  eight hits, including ordinary `ModuleCat.ExtendRestrictScalarsAdj` maps and
  `CategoryTheory.Abelian.Ext.homLinearEquiv`; none supplies this site statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed grep for the
  item ID in `lean/WeilConjectures`, found no already-stated complete node.
  Searches for `finiteHom`, `site.*Hom`, scalar/site comparisons, restriction units
  and derived coefficient maps found the four published finite-Hom interface
  modules above, which are reused. The parent `FiniteCoefficientHomChange` theorem
  concludes coefficient-Hom invertibility and does not replace this independent
  descent/monoidal-square statement; importing it would reverse the dependency.

Validation: the delivered module compiled through the prescribed `scompile.py`
against the live server library with exit code zero and no warnings. The final
statement has one `sorry`; every definition has real data, and every universe and
variable is explicitly bound. Server preflight and delivery are run next.

## Returned H3 repair

The immutable returned head was `03dcbeaffef9`. The initial required dry run of
its retained packet passed (`0ec22981c81`), confirming a mathematical H3 repair
rather than a compiler repair was needed. The sandbox node differs from the
current read-clone base only in `lean` and the permitted additions to `stmt_deps`.
No natural-language node statement is changed: its final sentence and proof step 7
already say that the etale equations imply the pro-etale equations.

`CoefFiniteHomSuccessive` now has the form `(etaleSuccessive ∧ etaleIdentity) →
(intrinsicSuccessive ∧ intrinsicIdentity)`. The first hypothesis quantifies over
all `r : ℕ`, `k : r ≤ m` and etale finite-Tor constructible `K,M`, and states the
successive equation using `finiteHomEtaleAssoc`, `finiteHomEtaleReduction` and
`etaleFiniteHomCanonical`. Its Hom transport has the inverse associator in the
contravariant input. The second hypothesis quantifies over all etale finite-Tor
constructible `K,M` at level `n` and states the identity equation using
`etaleFiniteHomCanonical (Nat.le_refl n)` and the published
`ProEtale.normalizedOriginScalarUnit`. This is the actual left-adjoint identity
comparison, with the self-quotient equality supplied by the existing Mathlib
`Ideal.Quotient.factor_eq` lifted via `RingHom.ulift`. The conclusion preserves
both previous intrinsic equations verbatim, including every finite-Tor domain.

The exact added dependency's source and full signature were read in
`Sheaf.Paper.NormalizedOriginScalarComparisons`; it is publicly imported and its
landed node ID is added to `stmt_deps`, as the return requires. The theorem proof
docstring's step 7 now explicitly records the etale-equation premises. No new
node or dependency module is necessary.

Focused reuse searches: `rg` for `normalizedOriginScalarUnit` and quotient identity
maps in `lean/Sheaf/Paper`, `lean/Sheaf/SixFunctors` and Mathlib's ideal-quotient
sources found `Ideal.Quotient.factor_eq` and the same normalized unit application
in `FiniteTargetChangeCoherence`. That latter downstream module is not imported;
we directly use the owning normalized-origin definition. No new unit definition
is introduced. The blueprint's current final paragraph and the item's proof step 7
were reread: associativity/uniqueness gives etale equations, and the site square
transports them. This item states that transport implication.

Repair self-check: both premises range over the original finite-Tor constructible
etale domain, every positive further quotient is included, and both conclusions
retain all intrinsic finite-Tor constructible pairs. The cases `n=m`, `r=m`,
`r=m=n` and exponent one remain included. The identity equation uses the canonical
unit on both Hom inputs and on Hom itself. There is still no invertibility claim
for either scalar-Hom arrow. The maintainer's note about the dependency's chosen
intrinsic associator and unitors is retained as a dependency issue for its later
fix, as directed; this repair changes only the returned H3 clause.

Repair validation: prescribed `scompile.py` completed with exit code zero; sandbox
and library module compilations took 24.5 s and 33.5 s respectively, with no
compiler errors or warnings. The Lean file has no line over 100 characters,
`autoImplicit false`, and exactly one postponed theorem proof. The recorded
main theorem signature remains verbatim; its final predicate now unfolds to
the requested implication. Dry run and delivery follow.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
