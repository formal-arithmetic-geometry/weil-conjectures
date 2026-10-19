## Worker report

The item is stated in `Sheaf.Paper.SitePerfectCoefficientDual`, with primary declaration
`WeilConjectures.sixFunctor_sitePerfect_dual`. Its only postponed proof is that theorem's
`sorry`. `WeilConjectures.sixFunctorCoefficientEvaluation` is a real construction of the
canonical evaluation, valid for each closed domain of the given datum. The theorem
has four conjuncts, spelling out every allowed coefficient choice rather than adding
an unrelated coefficient category as a parameter. The natural-language statement,
proof and proof dependencies of the item are unchanged.

Hypothesis and clause correspondence:

- The primes p and ell, the positive exponent a, q = p^a, the finite field k0 of
  cardinality q and its algebraic closure k are `D : FiniteFieldDatum.{u}` and
  `C : D.CoefficientDatum`. The fields of D are `p`, `a`, `q`, `prime`,
  `exponent_pos`, `cardinality_eq`, `k₀`, its field/finite instances, `card_base`,
  `k`, its field/algebra instances and `isAlgClosure`. C carries `l`, `prime`,
  `different : l ≠ D.p`, and the chosen Qbar with its algebraic-closure instance.
- A finite extension E/Q_ell is `(E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]`. Its integers, uniformizer and quotients
  are the existing Padic coefficient constructions, not extra chosen rings.
- All positive finite exponents are represented by `(n : ℕ)` with actual
  exponent `n + 1`; the datum receives `Nat.succ_le_succ (Nat.zero_le n)`.
  In `IsFiniteCoefficientSitePerfect ... n` the same exponent is already n+1.
  In particular n=0 here is the paper's exponent one, not a zero quotient level.
- The fixed six-functor datum is `S : SixFunctorDatum D C E (n+1) ...`.
  `X : SixFunctorSpace D` is an arbitrary finite-type scheme of that datum.
  No separatedness of X, smoothness, properness or nonemptiness is added.
- K in D^b_ctf is the full subcategory of
  `S.toSixFunctorOperationDatum.finiteTorDomain X` or `.integralFiniteTorDomain X`.
  At field stages the recorded finite-Tor convention is the whole constructible
  category, written as `(⊤ : ObjectProperty ...).FullSubcategory` for the
  intrinsic rational and general common-stage categories. Membership in the top
  property adds no mathematical assumption.
- Locally quasi-isomorphic to bounded finite-projective module complexes means
  respectively `IsFiniteCoefficientSitePerfect`, `IsIntegralCoefficientSitePerfect`,
  `IsSfRationalCoefficientSitePerfect`, and the ownership-preserving intrinsic
  common-stage interface `IsGeneralAlgebraicallyClosedCoefficientSitePerfect`.
  The first two use actual covering sieves and actual bounded module complexes
  via `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`. The rational predicate
  uses actual bounded complexes whose degree-zero terms are retracts of finite
  sums of the unit after localization; it never requires those retractions to
  lift integrally. The common-stage predicate asks for one perfect rational
  finite-field representative and an isomorphism to its actual inclusion.
- K dual = RHom(K,Lambda_X) is the EXISTING contravariant functor
  `(sixFunctorCoefficientDual (S.<stage>Closed X)).obj (op K)` from
  `Sheaf.Paper.SixFunctorDualNotation`. It fixes the second argument of
  `sixFunctorDomainHom` to the closed structure's coefficient tensor unit.
  The closed domains use exactly `sixFunctorFiniteHom`, `constructibleIntegralHom`,
  `rationalDerivedInternalHom`, and `commonStageDerivedInternalHom`. The integral
  underlying Hom is the ambient completed-ring-site Hom, not Hom into a
  dualizing object or an unrelated completion of a tensor operation.
- The first, second, third and fourth conclusions repeat the same site-perfectness
  predicate on that dual, respectively. `.obj.obj` forgets finite-Tor and bounded
  constructible membership at the finite/integral stages; `.obj` forgets only
  the top-property wrapper at the field stages. No cohomological amplitude bound,
  uniform covering bound or choice of global projective model is introduced.
- The evaluation clause is implemented, rather than merely existentially named:
  `sixFunctorCoefficientEvaluation (S.<stage>Closed X) K` has source
  `M.closed.tensor.obj (K, (sixFunctorCoefficientDual M).obj (op K))` and target
  `M.closed.monoidal.tensorUnit`. Its body is the given signed symmetry followed
  by `M.closed.evaluation K M.closed.monoidal.tensorUnit`, the specified adjunction
  counit. The symmetry changes the recorded Hom-tensor argument order into the
  displayed K-tensor-dual order. There is no arbitrary arrow, Nonempty choice,
  postponed definition data, extra invertibility assertion, or gluing hypothesis.

Statement dependency declarations read and used:

- `def-sf-datum`: `Sheaf.Paper.SixFunctorDatum`,
  `WeilConjectures.SixFunctorDatum`, its `SixFunctorClosedDomain`,
  `sixFunctorDomainHom`, and finite/integral/rational/common closed fields.
  The ambient and coefficient-change comparisons normalize these closed data to
  the recorded coefficient operations. The monoidal unit is the coefficient
  unit, including completed integral coefficients, as in the existing dual notation.
- `def-weil-site-perfect-complex`: `Sheaf.Paper.SitePerfectComplex`, all four
  stage predicates named above, with `IsRationalFiniteProjectiveTerm` and the
  covering-sieve/bounded-complex definitions read in full. The common intrinsic
  predicate is the §1(B) repair explained below.
- `def-weil-derived-pullback-tensor-hom`:
  `Sheaf.Paper.DerivedPullbackTensorHom`, `finiteIntrinsicDerivedInternalHom`,
  `constructibleIntegralHom`, `rationalDerivedInternalHom`,
  `commonStageDerivedInternalHom`, their permitted-pair domains and representative
  descriptions. These are used through the datum's actual closed domains;
  no private operations are constructed.
- Added landed statement dependency `def-sf-pf`:
  `Sheaf.Paper.SixFunctorDualNotation`,
  `WeilConjectures.sixFunctorCoefficientDual`. This existing generic functor
  is usable without the separatedness binder on its four stage-specific
  convenience definitions. Its full definition and docstring were read.

Proof plan: the theorem docstring carries all eleven node steps, including exact
slice restriction; separate degreewise finite-free retractions; exactness of term
Hom as a retract; the K-injective comparison and its signed bounded dual; actual
rational retractions; term comparisons; natural stupid-tail short exact sequences
and connecting squares; the signed shift; finite downward induction; passage to a
common coefficient field; and counit evaluation. Imports include the recorded
modules of the restriction, Hom complex, derived Hom, bounded exact-term Hom,
scalar localization, rational term comparison, stupid tails, derived SES triangle,
two-out-of-three, scalar extension and operation-reduction dependencies. The old
`sk-def-sf-operations` audit names finite étale upstream functors; for its adjunction
step the actual four-stage adjunction is already the public datum dependency's
`CoefficientClosedStructure.adjunction` and `.evaluation`, which are used directly.
No second copy of the upstream finite étale operations is needed.

Edge cases checked by reading the expanded predicates and sources before and after
writing: zero complex, zero-rank free summands (Fin 0), empty scheme, exponent one,
negative or shifted degree support and reversed/empty support intervals. Bounds
and ranks remain local and may vary with each covering member. Rational torsion
and rational splittings that do not lift integrally remain allowed. Common-stage
perfection uses existence of a finite-field representative, not a condition on
every integral representative. Coefficient and site size conventions are inherited
unchanged; `SitePerfectComplex` keeps independent site and coefficient universes,
and the item uses the single size already required by SixFunctorDatum. No universe
equality beyond that datum's existing signature is added. There is no disputed
statement and no statement correction.

Searches (prescribed msearch.py plus direct rg):

- LeanFinder: "A perfect complex of sheaves of modules has perfect derived internal
  dual and a canonical evaluation to the coefficient unit" returned eight hits:
  sheaf cohomology, Ext, K-projective and derived truncation statements. None
  states the four-stage site-perfect coefficient-dual assertion.
- Loogle: "Module.dual_projective, CategoryTheory.MonoidalClosed, ihom.ev" returned
  zero hits with unknown identifier `ihom.ev`. Direct reading of Mathlib found
  `Module.dual_projective` (ordinary modules) and
  `CategoryTheory.ihom.ev` evaluation, not this theorem.
- LeanSearch: "The derived internal Hom of a perfect complex of module sheaves
  into its coefficient unit is perfect" returned eight hits including ihom,
  MonoidalClosed.unitNatIso, internally projective objects and ordinary perfect
  pairings. These do not state site-perfect derived duality at the four stages.
- msearch grep: `perfect.*dual|dual.*perfect|IsDualizable` in Mathlib's
  CategoryTheory returned zero hits.
- rg of `prop-sf-dualizable`, sitePerfect/dual and perfect/dual combinations in
  `lean/WeilConjectures` and `lean/Sheaf` found the proof helper modules and
  related theorems. `CategoryTheory.ringedSitePerfectDuality` concerns one ordinary
  ringed site; the scheme perfect-duality results concern O_X-modules; the
  Poincare/locally constant dual results impose other hypotheses. None states
  this datum's complete finite/integral/rational/common-stage assertion.
- The declaration-name search in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` found the EXISTING
  `WeilConjectures.sixFunctorCoefficientDual` in SixFunctorDualNotation, which is
  reused. No existing `sixFunctorCoefficientEvaluation`,
  `sixFunctor_sitePerfect_dual` or
  `IsGeneralAlgebraicallyClosedCoefficientSitePerfect` was found.

Source checks: the current main-20261015 prop-sf-dualizable.md and its proof,
and the node's current eleven-step proof, were read. Stacks sites-cohomology.tex,
lemma-dual-perfect-complex (08JJ), agrees with the ordinary site-perfectness clause.
The coefficient-stage refinements are those already recorded by the item and its
three original statement dependencies.

Validation: scompile.py compiled both delivered modules separately in dependency
order against the live server build; both sandbox and library-path checks passed,
with no error and no non-sorry warning. The dependency module has no new sorry.
The item theorem has the sole new sorry, with the matching DAG node and complete
proof docstring. No proof is supplied in this stage.

## Dependency modules

`def-weil-site-perfect-complex`: the recorded common-stage predicate accepts
`algebraicallyClosedConstructibleCategory`, with legacy rational finite stages.
`SixFunctorDatum.commonClosed` and `commonStageDerivedInternalHom` instead accept
`generalAlgebraicallyClosedConstructibleCategory`, with intrinsic sf rational
finite stages. These are distinct interfaces, and the source expressly does not
identify legacy and intrinsic stage categories. The owning module is therefore
extended under §1(B), retaining every existing declaration and body. The appended
`IsGeneralAlgebraicallyClosedCoefficientSitePerfect` says exactly what the same
node's common-stage clause says: there exists a finite coefficient field and an
`IsSfRationalCoefficientSitePerfect` object whose actual stage inclusion is
isomorphic to K. It uses `GeneralAlgebraicallyClosedCoefficients.inclusion`, not an
arbitrary map or chosen equivalence. Only this dependency node's lean record changes,
with its required explanation in lean.note. No new DAG notion or definition node is
introduced.

## Second reading by NW

A separate rereading of the item, its dependencies and the final Lean was performed
by this worker; the dispatcher explicitly forbids starting another agent. The
maintainer's independent review remains the independent reading for this delivery.

The rereading matched D/C with every arithmetic and field hypothesis; checked the
n versus n+1 convention in both the datum and finite perfectness predicate;
checked X has no separatedness binder; checked the finite and integral subcategory
wrappers and the field-stage top wrappers; unfolded the existing coefficient-dual
functor to confirm its second argument is the coefficient unit; and checked all
four conclusions use the SAME local-model predicates as their hypotheses. It
checked the actual evaluation's source, symmetry direction and counit target.
The construction retains arbitrary K of each domain and does not depend on its
perfectness witness, which is exactly the assertion that evaluation is defined.

The rereading found the already published coefficient-dual functor, so the draft
object-only helper was removed and replaced by that functor's `.obj (op K)`.
This is why def-sf-pf was added to stmt_deps. It also found the legacy/intrinsic
common-stage mismatch; the ownership-preserving dependency extension repairs it
rather than adding a hypothesis identifying the two categories. Existing
SitePerfectComplex declarations and their bodies were compared with the base and
are unchanged. The final rereading found no remaining mismatch, no false clause,
no hollow data and no silent statement change. Both final files passed scompile.
