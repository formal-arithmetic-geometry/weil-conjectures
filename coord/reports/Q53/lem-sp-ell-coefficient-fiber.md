## Worker report

Delivery: `lean/Sheaf/Paper/EllCoefficientFiber.lean`, namespace
`AlgebraicGeometry.ProEtale`, with three postponed theorems belonging to the three
parts of this node: `sp_completed_coefficients_regular`,
`sp_ell_coefficient_tensor`, and `sp_ell_coefficient_fiber`.
Every proof is `by sorry`. All supporting definitions contain actual data.
The source is main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1,
read in full together with this node's eight expanded proof steps.

Hypotheses and coefficient conventions:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- Its actual valuation ring and chosen uniformizer are
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`, inherited from the tower dependency.
- An arbitrary scheme is `(T : Scheme.{t})`. No finite-field datum, characteristic,
  dimension, nonemptiness, or finiteness assumption is imposed on T.
- `u` and `t` remain independent; coefficients and module values use
  `max u (t+1)`. `spCoefficientModulesAbelian` specializes Mathlib's existing
  abelian instance with the already available sheafification and locally bijective
  witnesses in precisely this universe. It introduces no mathematical assumption.
- Every level index n in this file denotes the paper's positive exponent n+1,
  exactly as in `spCoefficientRing`. Thus `m ≤ n` means n+1 >= m+1 >= 1.

Clause-by-clause reading:

1. R is `completedIntegralCoefficientSheafUnrestricted l E T`, with its existing
   commutative version `completedIntegralCommRingSheafUnrestricted`. B_(n+1) is the
   dependency's `spCoefficientRing l E T n`. Uniformizer quotients are the existing
   `integralCoefficientSheaf l E T j`. The canonical ell projection
   `spCompletedEllProjection` composes the uniquely normalized cofinal-limit
   comparison from `sp_completed_coefficient_limit` with its limit projection.
   This is choice from a UNIQUE normalized isomorphism, never an arbitrary map.
2. The first conjunct of `sp_completed_coefficients_regular` is
   `∃ (e : ℕ) (v : Oˣ), 1 ≤ e ∧ (l : O) = (v : O) * π ^ e`.
   Its second conjunct writes both inclusions witnessing cofinality of the
   `spEllIdeal` and `Padic.coefficientExtensionIdeal` powers.
3. Its third conjunct asserts `Finite` for both O/(ell)^(n+1) and O/pi^(n+1).
4. Its fourth conjunct asserts `Mono` for every positive power of multiplication
   by the actual completed constant ell and pi sections. A mono of module sheaves
   is sectionwise injective, since kernels are sectionwise. Power zero is identity.
5. Its last two conjuncts give the quotient isomorphisms as module-sheaf cokernels,
   normalized by `cokernel.π ... ≫ e.hom = spRingModuleMap ...`. These are the
   canonical projections to the finite constant R-algebras, not a stipulated quotient
   notation: the normalized module quotient identification supplies the ring quotient
   identification too, since multiplication and one descend uniquely through that
   projection. The actions are the actual restriction actions of these ring maps.
6. The same last conjuncts state
   `CochainComplex.IsKFlatResolutionIndependentCoefficients` for the augmentation
   `principalAugmentation ... ≫ (singleFunctor _ 0).map e.hom` in both cases.
   `principalKoszul` is the existing scalar cone on R[0], hence its only terms are
   the two rank-one free modules R in degrees -1 and 0. This is precisely the
   finite free K-flat resolution required by the node.
7. `spCompletedQuotientTensor` uses the existing `koszulTensorFunctor`, i.e. the
   actual sheaf tensor and `CochainComplex.mapBifunctor` totalization.
   `sp_ell_coefficient_tensor` identifies B_(n+1)[0] tensor K_(m+1) with the
   explicit scalar cone having differential `l ^ (m+1) • 𝟙 B_(n+1)`.
8. `spRelativeCoefficient N n hn` is B_(n+1) restricted along the actual quotient
   B_(N+1) -> B_(n+1). `spRelativeReduction` is its actual coefficient reduction,
   built from the ring triangle and the tower functor's composition law.
   The arbitrary common upper level N is a way to write semilinear transitions
   in one category. N=n recovers complexes over B_(n+1); N=n' puts a transition
   and both its comparisons over B_(n'+1). Every pair n' >= n is covered by N=n'.
9. `spRelativeKoszul` is the two-term scalar cone representing P_(n+1,m+1).
   In `SpRelativeFiberComparison`, the epsilon normalization
   `mappingCone.inr ... ≫ ε = (singleFunctor _ 0).map spRelativeReduction`
   forces exactly reduction in degree zero. In the other degree its target is zero,
   so this specifies the augmentation uniquely.
10. `spRelativeFiber ... ε` is the ACTUAL `mappingCone ε` shifted by -1.
    `spRelativeFiberLeft`, `Middle`, and `Right` are the canonical cone and
    shift projections to the coefficients in degrees -1, 0, 1. Mathlib's cone
    differential has exactly the negative reduction in the last position.
11. The existential map `a : B_(m+1) -> B_(n+1)` is normalized by
    `spRelativeReduction ... ≫ a = l ^ (n-m) • 𝟙 B_(n+1)`.
    As reduction is epi this determines a uniquely, with local formula
    x mod ell^(m+1) -> ell^(n-m)x mod ell^(n+1). Its `Mono` conjunct is explicit.
12. `i` has source `(singleFunctor _ (-1)).obj B_(m+1)`, the standard
    cochain representative of B_(m+1)[1]. The equation for `i.f (-1)` and
    `spRelativeFiberLeft` fixes its degree -1 component to a. Its other source
    terms vanish, so all its other components are zero. `QuasiIso i` asserts
    the precise specified comparison is a quasi-isomorphism.
13. The three `Nonempty` isomorphism statements in `sp_ell_coefficient_fiber`
    give H^-1(P) = image(ell^(n-m)) isomorphic to B_(m+1), and
    H^0(P) isomorphic to B_(m+1). Here `image` is the categorical image sheaf,
    including sheafification, rather than an incorrect sectionwise-image presheaf.
14. For every n' >= n and every normalized comparison at n', the existential r
    is a chain map whose three coordinate equations are respectively
    (reduction, reduction, identity). These equations uniquely specify the
    canonical coefficient reduction on the actual shifted cones. The final
    equality `i' ≫ r = (l ^ (n'-n) • 𝟙 _) ≫ i` is the chain-level transition
    square. Inverting the displayed quasi-isomorphisms gives exactly the node's
    multiplication-by-ell^(n'-n) description in the derived category.

Dependency declarations read and used:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientRing`,
  `spCoefficientRings`, `spCoefficientReduction`, `spEllIdeal`,
  `sp_completed_coefficient_limit`, `sp_coefficient_ideals_cofinal`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the statement is expressed already
  at the chain/quasi-isomorphism level, before applying this localization.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`.
- Added existing statement dependency `def-pur-principal-koszul-quotient-towers`,
  whose recorded module `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`
  supplies `principalKoszul`, `principalQuotient`, `principalAugmentation`,
  `globalSectionMultiplication`, `endoPow`, and `koszulTensorFunctor`.
- `Sheaf.Paper.CompletedIntegralCoefficients` and
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the unrestricted
  completion, finite uniformizer quotient system, its commutative version and
  canonical constant-scalar map.
- Proof imports retain `CompletedIntegralScalarRegular`,
  `CompletedIntegralProjectionDivisibility`, `SiteSheafificationSectionsLocal`,
  and `KFlatTensorConeTwoOutOfThree`. The coefficient extension/finite DVR
  statements and constant sheafification come through the existing tower module.

Edge cases checked before writing: n=m (including n=m=0, i.e. paper level one)
leaves zero first differential, a=identity, and a contractible [-identity] tail;
n'=n gives identity power and identity reduction; n'-n >= m+1 makes the
transition on B_(m+1) zero; ramification e>1 still gives cofinal filtrations;
T empty is allowed, with zero module sections and mono scalar maps; arbitrary
characteristic and distinct site/coefficient universes are retained. The field
extension is not restricted to the unramified case or to a fixed algebraic closure.

Searches for an existing exact statement (2026-10-21):

- `msearch.py ... leanfinder "For n at least m the fiber of the quotient Koszul
  augmentation is the shifted quotient with power multiplication transitions"`:
  eight hits, including `AdicCompletion.transitionMap`, `Submodule.factorPow`,
  and ideal ramification quotient maps. None states this sheaf/fiber result.
- `msearch.py ... loogle '"Koszul", "homology"'`: zero hits.
- `msearch.py ... leansearch "The homotopy fiber of a quotient Koszul augmentation
  has power multiplication transition maps"`: eight general homotopy, quotient,
  and polynomial-fiber hits, no match.
- `msearch.py ... grep 'Koszul.*(quotient|homology)|quotient.*[Nn]onzero[Dd]ivisor'
  Algebra`: only the future-work comment in `Algebra/Homology/LocalCohomology.lean`.
- `rg` in both project roots for the node id, `quotientKoszul`, and
  `ellCoefficientFiber`: no exact statement. Broader Koszul searches found and
  reused the existing principal Koszul/quotient construction instead of copying it.

No new independent definition nodes, dependency-record replacements, or statement
corrections. No STATEMENT-DISPUTED issue. The generic ring-map helpers and specialized
coefficient/cone projections belong to this node's canonical constructions and are all
listed in `lean.declarations`, with source/blueprint docstrings.

Validation: the full module compiles through scompile.py in roughly 27 seconds per
file. A first direct specialized reduction-map construction exceeded the kernel
checking limit; factoring its scalar-linearity proof through the generic commuting
ring-triangle constructor repaired this without changing a statement or raising a limit.

## Second reading by Q53

I reread the node and the complete final file as the sole dispatched worker; no
additional agent was started, as required by the brief. The maintainer's independent
review remains the separate independent review of this delivery.

The second pass checked all fourteen clauses above against the signatures, the
positive-level offset, the actual cone shift and signs, and the fully specified
transition coordinates. It verified that epsilon, a, i and r are normalized by
coordinates, rather than arbitrary quasi-isomorphisms or unconstrained arrows.
The common-upper-level formulation is equivalent to restriction along quotient
ring maps and does not exclude the diagonal n=m or n'=n cases. It also checked that
the tensor model uses the existing total tensor, and that quotient isomorphisms
commute with the canonical quotient projections. The needed existing principal
Koszul node was added to stmt_deps. No mathematical mismatch or statement change
was found. The only implementation repairs were explicit universe specialization
and factoring the reduction-map constructor to avoid expensive kernel unfolding.
