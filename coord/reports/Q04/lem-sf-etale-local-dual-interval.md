## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalDualInterval` states
`AlgebraicGeometry.Etale.etaleLocalDualInterval`, with its whole proof `sorry`.
There are no new definitions, auxiliary postponed theorems, or changes to the
natural-language node. Its docstring carries all four proof steps and their nodes.

Hypotheses and clauses, matched against the node:

- A finite commutative ring and arbitrary scheme are `(A : Type (u + 1))
  [CommRing A] [Finite A] (T : Scheme.{u})`. This follows the recorded ordinary
  module-sheaf size convention; every finite ring can be lifted to this universe.
- The ordered interval and arbitrary shift are `(a b m : ℤ) (hab : a ≤ b)`.
- `P : DerivedCategoryModule A T` is precisely the recorded ordinary small-etale
  module-sheaf derived category. `U : Scheme.Cover etalePrecoverage T` is its
  etale covering, `E` its family of module cochain complexes, and `hP` says that
  derived restriction of P is the localization of the termwise constant complex.
- `hE` expresses finite projective exactly by retraction maps `s`, `r` to and
  from `ModuleCat.of A (Fin n → A)` with `s ≫ r = 𝟙 _`. No freeness or chosen
  basis is required for E. `hEzero` says every term outside `[a,b]` is zero.
- A module sheaf L is the explicit `Sheaf T.smallEtaleTopology (ModuleCat A)`
  binder. Its separate covering V and `hL` give local isomorphisms to the
  constant module A. No global trivialization is assumed.
- `H` and `hH` only name the object `derivedHom(P, singleFunctor(L,0)[m])`.
  Quantifying H with this equality is equivalent to substituting that expression
  everywhere. This does not impose any extra condition on P or L.
- The existential W, its index maps σ and τ, maps r and s, and their two
  equations express a common refinement of U and V. Each W member also has
  the asserted trivialization of L. Maps between etale T-schemes commuting
  with their structure morphisms are automatically etale; no arbitrary maps
  are substituted for the cover or its restriction functors.
- On W_k the existential module cochain complex D and its family of isomorphisms
  `e q : D.X q ≅ ModuleCat.of A (Module.Dual A ((E (σ k)).X (-q)))`
  specify the degree-q term of the unshifted dual. The displayed equation for
  every q and φ transports `D.d q (q+1)` through e and says exactly
  `d(φ) = (q+1).negOnePow • φ.comp (E.d (-(q+1)) (-q)).hom`.
  Integer `negOnePow` is the signed unit (-1)^(q+1), including negative q.
  The adjacent differential and all term isomorphisms determine the whole
  cochain complex up to isomorphism, since nonadjacent differentials are zero
  by the cochain-complex shape axiom. Thus D is the specified dual complex,
  rather than an arbitrary representative with no differential condition.
- The next `Nonempty` isomorphism says H restricted to W_k is Q of the
  termwise constant D shifted by m. This is `Hom_A(E,A)[m]`.
- The retractions for `(D⟦m⟧).X q` assert finite projectivity of every shifted
  model term; the following IsZero clause asserts its support in
  `[-b-m,-a-m]`. Its sheaf terms are constant because the entire model is the
  image of the constant-sheaf functor on complexes.
- `∀ i, Scheme.IsFiniteLocallyConstantSheaf (homologyFunctor.obj H)` is finite
  locally constant cohomology, using the recorded definition. Its stalkwise
  finite generation is equivalent to finite stalks over our finite A.
- `DerivedCategory.isBoundedConstructible A T H` uses the exact recorded
  bounded-constructibility predicate with finite constant module values on
  constructible locally closed strata.
- `DerivedCategory.hasTorAmplitudeIn A T (-b-m) (-a-m) H` is the recorded
  predicate quantifying over EVERY degree-zero module sheaf, with the
  recorded unbounded `derivedTensor` and vanishing `homologyFunctor` outside
  the stated interval. It is not just a support assertion for H alone.

A constant complex is expressed as the image of a complex of A-modules under
`constantSheaf.mapHomologicalComplex`. This loses no locally represented P:
if “complexes of constant modules” is read as allowing sheaf differentials,
refine the original cover to make those differentials constant. There are
only finitely many relevant differentials, between finite modules (A is
finite and the terms are finite-free retracts), so a simultaneous etale
refinement exists. The node itself supplies that refinement interpretation
in its reviewed disconnected-cover edge case. The theorem is stated for
every supplied cover and constant complex model, and supplies a common
refinement of it and the line cover.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, together with its
  coefficient import: `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  `DerivedCategory.Q`, `DerivedCategory.singleFunctor`, and
  `DerivedCategory.homologyFunctor`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its representative
  comparison. This is the generic ringed-site K-injective construction.
  For the ordinary module-sheaf encoding required by this node, the exact
  existing specialization is
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`,
  `AlgebraicGeometry.Etale.derivedHom`. Its source imports and constructs the
  K-injective right-derived internal Hom and the tensor-Hom adjunction in
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`.
  Uniqueness of that right adjoint identifies the two constructions under
  the constant-ring/module-sheaf equivalence. We reuse this canonical existing
  functor without defining a new Hom or assuming an arbitrary comparison.
  The generic recorded module remains publicly imported. No dependency node
  needs changing: this is an existing concrete realization of its notion.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
  Its current source was read using `scompile.py --source` because the
  upstream checkout predates that module.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, used through Tor amplitude.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` and its coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`. The owning
  module adds only the lower-bounded variant, which is not substituted here.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` supplies
  derived upperStar; ordinary and derived upperStar along etale maps are
  the exact restriction to their small etale sites.

The six other stated proof dependencies are imported without `public`, as
required: `DerivedCategory.FlatModel`, `BoundedExactTermHomQuasiIso`,
`LocalizedModuleExactIndependent`, `FiniteFreeInternalHomExact`,
`RingedInternalHomExactRestriction`, and `PbcActualScalarPullback`, under
the roots in their recorded modules. These imports preserve the stated
proof plan. No attempt is made at stage 2 to prove any of its comparisons.

Edge cases checked before and after writing: E = 0 permits rank-zero
retractions; a=b gives an unshifted one-term dual in degree -a and shifted
degree -a-m; m=0 gives [-b,-a]; m positive or negative uses cochain shifts
and integer signs with no positivity restriction. Empty schemes and empty
cover index types are permitted (all local obligations are universal and
vacuous for an empty index); no Nonempty or nonzero-ring binder excludes
them. Disconnected schemes and different local ranks are permitted by
rank n depending on the cover member and degree. Zero coefficient rings
are included. There is no characteristic, finite-type, Noetherian,
separatedness, field, or global trivialization assumption.

Searches for the exact statement and existing constructions:

- `msearch.py leanfinder`, “Derived dual of etale locally constant finite
  projective complexes has reversed shifted Tor amplitude”: eight hits
  concerning projective Tor vanishing, projective derived maps, t-structure
  support and K-projective shifts; no matching etale dual theorem.
- `msearch.py loogle`, `ModuleCat.dual, CochainComplex, Module.Projective`:
  unknown identifier ModuleCat.dual; no hits.
- `msearch.py grep`, `localDual|LocalDual|strictlyPerfect|StrictlyPerfect`
  in CategoryTheory: zero Mathlib hits.
- `msearch.py leansearch`, “Derived internal Hom into shifted locally
  constant rank one sheaf has finite projective local dual model and negative
  reversed Tor interval”: Module.dual_finite, Module.dual_projective,
  sheafHom, Ext.homEquiv, and shift/condensed/projective-resolution results;
  none states the local etale model or the interval theorem.
- `rg` in the upstream WeilConjectures and published Sheaf sources for the
  theorem name and local-dual/finite-projective/derived-Hom vocabulary:
  no exact theorem. The existing ordinary derivedHom was found and reused.
  Generic `CochainComplex.rightDual` exists for complexes whose terms have
  chosen monoidal right duals. Its degreewise dual choices need not be
  definitionally Module.Dual, so the theorem describes the same signed dual
  by term isomorphisms and differential equations instead of introducing a
  second construction or imposing dualizability instances as hypotheses.
- The requested upstream grep of this node id returned no hit. DAG search
  located the finite-projective dual and finite-projective Hom siblings,
  but none states this local shifted interval assertion.

No statement dispute or correction.

Validation: scompile.py compiled the module in both its private sandbox
and library-path confirmation, with no errors or unexpected warnings.
The module has one theorem, whose entire proof is `sorry`; every variable
and universe is explicitly bound and autoImplicit is disabled. Lines are
at most 100 characters. The prescribed delivery preflight is run separately.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
