## Worker report

The new module `Sheaf.Paper.RootTowerInnerSupport` states
`AlgebraicGeometry.ProEtale.RootInnerSupport.rootTower_inner_support` with one
`sorry`. All other declarations are real helper definitions owned by this node.
There are no new nodes, dependency repairs, or statement corrections.

The source is the exact agent-expanded seven-step proof recorded in the node,
placed at paragraph (3) of the current blueprint's direct-image stability proof.
I opened that blueprint paragraph: it gives the direct-image stability reduction,
not an independent reference for this stronger all-continuous root-tower input.
The node already records the exact all-continuous reference as WANTED. I retain
that source status and its unchanged mathematical assertion.

Hypothesis and clause correspondence:

- Distinct primes: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)`.
- Characteristic-p field: `(k : Type u) [Field k] [CharP k p]`.
- Finite norm-topological extension: `[NormedField E]`,
  `[NormedAlgebra ℚ_[ℓ] E]`, `[FiniteDimensional ℚ_[ℓ] E]`.
- Algebraic closure with the extended norm: `[NormedField Ω]`,
  `[NormedAlgebra E Ω]`, `[IsAlgClosure E Ω]`. No completeness assumption.
- The two allowed coefficients are the two conjuncts `Assertion E ... E` and
  `Assertion Ω ... E`. `RootBoundary.coefficients` is the existing
  `Profinite.continuousCoefficientRingObj`, with all continuous functions.
- `RootBoundary.SiteMod` uses internal module objects over `condensedRingObj`
  on `Scheme.ProEt.topology`. `pullD` and `pushD` are the recorded exact inverse
  image and total unbounded derived direct image, not derived abelian images.
- Regular separated finite-type Y: `IsRegularScheme Y`, and
  `LocallyOfFiniteType y`, `QuasiCompact y`, `IsSeparated y` on its structure
  map `y : Y ⟶ Spec (.of k)`. This explicit map follows the boundary dependency.
- Affine etale chart: `A`, `CommRing A`, `b : Spec (.of A) ⟶ Y`, `[Etale b]`.
- Reduced SNC divisor: `H`, `hH : IsStrictNormalCrossingsBoundary H`.
  `hproduct` identifies its actual ideal with the parameter product ideal.
  `hbranches` says that the zero loci of the supplied parameters are exactly
  the irreducible-component supports of H, as in the boundary dependency.
- Affine pro-etale U: `R`, `CommRing R`, `a : A →+* R`, and
  `[WeaklyEtale (Spec.map (CommRingCat.ofHom a))]`, using the recorded small-site
  convention. All tower parameters are precisely `fun i ↦ a (s i)`.
- T, its prime-to-p positive root orders, power and transition relations,
  S and i are the already defined `RootBoundary.tower`, `stratumScheme`,
  `stratumInclusion`, and `boundary`. No copy of a root algebra is introduced.
  The root algebra's relations include x_(d,n)^n=t_d and
  x_(d,n)=x_(d,m)^(m/n) when n divides m.
- The partition is encoded by `out : Finset (Fin r)` and its complement
  `Finset.univ \ out`, which is required nonempty. This parametrizes exactly
  all partitions I_o disjoint union I_i, without an ordering or enumeration.
- V is an arbitrary presentation of the outer principal open: `IsOpenImmersion a`
  and `Set.range a = outerOpen t out`. W is `allOpen t`. The closed immersion
  `h` has reduced domain and exactly the inverse image of the complement of W;
  these properties characterize the node's reduced closed complement.
- T^circ is the existing `RootBoundary.puncture`; it inverts all the parameters.
  `test` is the recorded actual scheme X[P], not a discrete replacement.
- The finite-dimensional model has the unrestricted finite-dimensional
  `M : Type u`, `[AddCommGroup M]`, `[Module E M]`, `[FiniteDimensional E M]`.
  The dependency's `model F E M` condenses F tensor_E M with its module topology.
- The supplied lisse extension is `N : SiteMod F (tower p t)` with the recorded
  `IsLisseCoefficientModule`. Its boundary identification is the explicit
  isomorphism `e : i^*N ≅ (pointPull F S).obj (model F E M)`.
- Every profinite P is quantified in the scheme universe. `puncturedModule`
  uses the exact existing pullback of N[0] to T^circ[P].
- `f` is the structural factorization through V, specified by
  `wf : f ≫ a = vP p t P`. An open immersion is monic, so this is the unique
  required map, not an arbitrary replacement or an additional geometric
  assumption. `term` is precisely `R(f_P)_*(N_P[0])`.
- `closed` is `Rh_*h^*K`. For the closed immersion the ringed open/closed
  exactness theorem identifies Rh_* canonically with the exact h_* in the
  node. `supported` is exactly s^*Ra_* of that object.
- `delta` is obtained by applying the actual `derivedAdjunction` unit for h,
  then `pushD a` and `pullD s`. No abstract arrow is substituted for eta_h.
- `target` is the boundary dependency's p_S^* of right-derived internal Hom
  from its free internal coefficient module C_F[P], derived in the second
  variable. The existing free-module, tensor/Hom and condensation definitions
  are used without changes.
- `composition` uses `pushComp`, the canonical derived composition comparison,
  and the equation wf. It identifies s^*Ra_*K with the boundary theorem's
  s^*R(v_P)_* source in the required orientation.
- The first assertion conjunct supplies a normalized boundary alpha, so
  comparison existence is not hidden behind a potentially empty quantifier.
  For EVERY alpha satisfying the dependency's exact `Normalization`, the next
  conjunct supplies an isomorphism sigma in the derived category and states
  `delta ≫ sigma.hom = composition.hom ≫ alpha.hom`.
- `NaturalComparison` specifies the commuting squares for the actual unit and
  sigma. `ambientMap`, `closedMap`, and `supportedMap` are constructed from
  the actual geometric exchange mates and the supplied module arrow, without
  using inverse delta or sigma in their definitions. Its premise about alpha
  is exactly the ambient naturality square already supplied by
  `RootBoundary.ModuleNaturality`, `ParameterNaturality`, and `FamilyNaturality`.
  It is a diagram-transport formulation: given that known ambient square and
  the target's normalization, it asserts the supported square, as well as the
  unit square. Thus the input geometric map is never assumed already to
  commute with sigma. The primed schemes and maps range over entire schemes;
  they include pro-etale base changes and actual Q-parametrized family maps.
  For parameter restrictions use the test-map exchange on f; for maps of
  extensions use pushforward of the pulled-back module map; for tower actions
  use the entire test-scheme morphism and the supplied equivariant module map.
  The target arrow beta is the corresponding actual target-module,
  parameter-restriction or `parameterTargetTransport` map of the dependency.
- No invariants, total root nerve or coefficient-scalar compatibility beyond
  that in this node is asserted. Every displayed comparison is in the
  ordinary unbounded derived category, not merely its cohomology objects.

Dependency declarations read and reused:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse` and its underlying ring object;
  the boundary framework uses its scheme-universe all-continuous presentation
  `Profinite.continuousCoefficientRingObj` from
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `upperStarFromPoint`, `profiniteToProEtOf`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its action
  and action-compatible morphism structure.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`; the boundary framework's
  pullback/adjunction/composition declarations specialize the same framework.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `Scheme.proEtale_ringed_open_closed`, supplying closed direct-image exactness.
- `Sheaf.Paper.RootTowerBoundaryAcyclicity`:
  `RootBoundary.rootTower_boundary_acyclicity`; its public interfaces
  `RootBoundary.Normalization`, `openSource`, `target`, `pulledOpenModule`,
  `derivedAdjunction`, `pushComp` and the three naturality predicates are used.
- All recorded proof dependencies have imports: root puncture invariance,
  adjunction-normalized derived composition, coordinate-face comparison,
  finite closed-cover resolution, and SNC root-limit normal charts. The
  coordinate-face module supplies the canonical `squareUpper` and `exchange`.

Edge cases checked before and after writing:

- Empty out is allowed: the outer product is 1, hence V is the whole base.
- Nonempty inner set is retained; r=0 therefore has no eligible partition,
  exactly as in this node (unlike the broader boundary-acyclicity input).
- One inner branch yields the single-term closed-cover calculation.
- Rank zero is allowed: no nonzero module or positive-rank hypothesis occurs.
- Empty stratum S and empty P are allowed, with the usual zero derived objects.
- No finite P, discrete family, completed Omega, nonempty chart, connectedness,
  or equality of site object and morphism universes is imposed.
- Scheme and parameter universes are u; coefficients and sites use the recorded
  u+1/u small-site convention through the existing dependency interfaces.
- Naturality contains no evaluation-at-point tests; arbitrary entire primed
  schemes are quantified, so Q-parametrized equivariance is included.

Searches made with msearch.py, group NF and this item:

- leanfinder: `Derived restriction to inner closed support of a root tower with outer punctures`.
  Eight unrelated derivation/support hits, including Derivation.restrictScalars
  and support_deriv_subset; no matching theorem.
- loogle: `IsClosedImmersion, Adjunction.unit`.
  Zero hits (unknown identifier IsClosedImmersion on the search service).
- grep: `(rootTower|Kummer).*(support|closed)|(innerSupport|inner_support)`.
  Zero Mathlib hits.
- leansearch: `Derived restriction to inner closed support for compatible prime to characteristic root towers`.
  Eight unrelated polynomial/module/measure-support hits; no matching theorem.
- rg of both lean/WeilConjectures and lean/Sheaf for
  `rootTower.*inner|inner.*[Ss]upport|InnerSupport`: no duplicate. Existing
  PartialKummerBoundaryUnitModel cites the item as a proof input, but states
  a downstream group-invariants comparison, not this one-term assertion.
- rg of the upstream tree for the exact item id: no existing declaration.

Validation: scompile.py compiled both its sandbox probe and the named library
module cleanly, approximately 8.2 seconds each. The file sets autoImplicit false;
all variables and the single universe are explicitly bound. The only postponed
proof is the named main theorem, whose docstring includes all seven DAG steps.

## Second reading by NF

Dispatcher-started single-worker self-check; no independent second worker was
started, in accordance with the explicit brief. The maintainer's independent
review remains the independent reading of this delivery.

I reopened the node and checked the fields against the final file, especially
the two coefficient conjuncts, the nonempty inner complement, reduced Z,
unique structural factorization, the direction of composition, the exact
closed unit, and normalized sigma. The draft's term helper initially placed P
after its first use; this was corrected before compilation by binding P before
f. All helper data is explicitly constructed. The naturality target is not an
arbitrary identification: alpha retains the dependency's restriction-of-sections
normalization, and supportedMap is independently defined by exchange mates.
The final self-check found no mismatch requiring a node correction.

The required deliver2.py --no-push dry run passed server preflight and compilation
(commit eca532d03c9; nothing pushed by that dry run).
