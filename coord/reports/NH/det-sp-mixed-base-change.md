## Worker report

`Sheaf.SecSmoothPurity.MixedBaseChange` states
`AlgebraicGeometry.ProEtale.mixedBaseChange`, with `sorry` as its sole postponed
proof. The saved packet passed the required first dry run (891a316d2f), but the
required self-check found a mathematical mismatch: the old `βA`, `βB`, `c`, `c'`,
`eA`, `eB` were arbitrary maps, and invertibility did not specify the node's
canonical comparisons. The old exceptional functors also had an ambient domain,
whereas the dependency supplies adjoints on Dctf. This delivery repairs those
interfaces rather than retaining a false statement about arbitrary maps.

The node's natural-language statement, dependencies and proof remain unchanged.
There is no statement correction and no disputed mathematical assertion.

Hypothesis-by-hypothesis correspondence:

* The standing prime and positive characteristic assumptions are `ℓ`, `pchar`,
  `[Fact ℓ.Prime]`, `hp : 0 < pchar`, `hℓ : pchar ≠ ℓ`, `[Field k]`,
  `[CharP k pchar]`.
* The schemes are `X`, `Y`, `X'`, `Y'`. Their `Over (Spec (.of k))` instances,
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` instances on their
  structure maps say exactly separated finite type over k. The `IsOver`
  instances on `f`, `f'`, `g`, `g'` say that every arrow is a k-morphism.
* Smoothness and pure relative dimension d are `[SmoothOfRelativeDimension d f]`
  and `d : ℕ`, using the dependency's recorded Mathlib notion.
* `sq : ChosenCartesianSquare g' f' f g` supplies the Cartesian square, including
  its identification with the chosen fibre product and both projection equations.
* `cpt : Compactification f` supplies the open immersion `cpt.i`, proper map
  `cpt.g` and factorization. The finite-type, separated and k-structure instances
  on `cpt.Z` and the two `IsOver` instances keep this compactification in the
  standing setting. `mixedPullbackCompactification sq cpt` is literally the
  dependency's `Compactification.ofIsPullback`, and is used everywhere primed.
  In particular neither coefficients nor the comparison maps change the compactification.
* `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]`, `hA`, `hB`
  and `φ : A →+* B` express precisely finite commutative rings annihilated by
  powers of ℓ and their unital ring map. The powers may differ; there is no
  flatness, projective-dimension, nonzero-ring or residue-DVR assumption.
* The category `proEtaleDerivedCategory T R` is the existing ordinary uncompleted
  intrinsic constant-ring module derived category. `spFiniteConstructibleTorCategory`
  is the existing full subcategory for bounded intrinsically constructible
  cohomology and finite Tor amplitude; no etale-origin witness replaces its objects.
* Scalar extension is the actual `scalarExtensionFunctor φ T` from the dependency,
  not an endofunctor forgetting B's action. The certificates `hSX`, `hSY`, `hSXp`,
  `hSYp` express its already established Dctf membership and are used only in
  `reductionCtfScalar`, which changes neither underlying objects nor arrows.
* `hFA`, `hFB`, `hFAp`, `hFBp` likewise only express that the actual `Rp_* j_!`
  lands in Dctf. `reductionCtfCompactSupport` is the dependency's full-subcategory
  restriction. `GA`, `GB`, `GAp`, `GBp`, and `adjA`, `adjB`, `adjAp`, `adjBp`
  specify exactly the constructible adjunctions used to define the exceptional
  functors. They are not unconstrained functors, nor ambient adjoints. Quantifying
  over their presentations is harmless: right adjoints with their adjunctions are
  uniquely identified by the counit-preserving comparison. The dependency
  `reductionExceptional_isIso` supplies such presentations for f and f'.
* `hVA`, `hVB` certify the existing pullback's Dctf membership, needed to apply
  the primed right adjoints. `mixedCtfPullback` only lifts that same functor
  through the existing full subcategory. These certificates are the preservation
  assertions already used in Step 4 of the node, not additional geometric hypotheses.
* The node's b and b' are exactly `reductionDirectImageComparison` at cpt and its
  pullback. The node's beta is exactly `mixedCompactSupportExchange`, a real
  construction: whisker the canonical proper `directImageConstantExchange` by
  the actual open extension, then apply the primed proper pushforward to the
  actual open base-change map. `mixedOpenBaseChangeIso` transports the recorded
  `ordinaryOpenExtensionBaseChangeIso` through the canonical intrinsic realization;
  `openSquareDerivedPullbackModel` supplies its section-unit-normalized coordinate
  changes. The intermediate realization units are the published equivalence units.
  This is the compactification formula in Step 4, with no free exchange parameter.
* c and c' are natural transformations between the restricted actual operations.
  `hc` and `hcp` fix them by `b ≫ F_B(c) ≫ ε_B = S(ε_A)` and its primed version.
  This is precisely the dependency's defining equation multiplied by b on the
  left. Since b is invertible on Dctf by `reductionDirectImage_isIso`, this equation
  specifies the same unique transpose and does not ask for the mixed identity.
* `eA` and `eB` have exactly the domains `u_R^* f_R^!K` and targets
  `(f')_R^! v_R^*K`, on Dctf. `heA`, `heB` fix them by
  `β_R(f_R^!K) ≫ F'_R(e_R(K)) ≫ ε'_R = v_R^* ε_R`.
  Invertibility of the specified beta on these inputs makes this exactly the
  transpose of `β_R(f_R^!K)⁻¹ ≫ v_R^* ε_R` in the node. Thus these are defining
  equations for the named maps, not arbitrary arrows and not extra mixed-square
  assumptions. No invertibility on all ambient derived objects is assumed.

Clause-by-clause correspondence:

* The first conjunct, quantified over `M : spFiniteConstructibleTorCategory X A`,
  is the compact-support identity. Its left side is the inverse scalar/pullback
  identification at `Rf_!M`, then `v_B^*(b(M))`, then the actual beta_B at `M_B`.
  Its right side is scalar extension of the actual beta_A, then the actual b'
  at `u_A^*M`, then the primed support functor applied to the inverse scalar/pullback
  identification at M. This is exactly the first displayed equality with both
  evident identifications written out.
* The second conjunct, quantified over `K : spFiniteConstructibleTorCategory Y A`,
  has left side `S_X'(eA K) ≫ c'(v_A^*K)`. Its right side is the inverse
  scalar/pullback identification at `GA K`, followed by `u_B^*(c K)`, followed
  by `eB(K_B)`, and finally `GBp` applied to the scalar/pullback identification
  `v_B^*(K_B) → (v_A^*K)_B`. That last factor is required to identify the targets;
  the saved packet had hidden it inside a freely specified eB. The repaired
  statement makes it explicit and uses the actual B-category argument for eB.
* Both equalities are expressed on underlying morphisms in the ordinary intrinsic
  derived categories. The specified functors and the standing preservation facts
  put the endpoints in the node's Dctf categories. Since these are full
  subcategories, this is exactly equality there, without forgetting scalar action.

Dependency declarations read and used:

* `sk-def-sfb-dc-setting`: the setting docstring and
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  The older local checkout lacks this module; it was read through the authorized
  `scompile.py --source` interface. Its scheme assumptions are rendered explicitly.
* `def-cbc-compact-support-square`: `AlgebraicGeometry.Compactification.ofIsPullback`
  and `isPullback_i_ofIsPullback`, in `WeilConjectures.Compactification.BaseChange`.
* `def-sbc-smooth-morphisms`: `AlgebraicGeometry.SmoothOfRelativeDimension`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
* `det-sp-scalar-extension-functor`: `scalarExtensionFunctor`, its K-flat computation
  and `scalarExtensionFunctor_preserves_constructible_tor`, in
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.
* `det-sp-reduction-direct-image`: `reductionDirectImage_isIso` in
  `Sheaf.SecSmoothPurity.ReductionDirectImage`, with the reexported actual
  `reductionCompactSupport`, `reductionDirectImageComparison`,
  `directImageConstantExchange` and `directImageScalarPullbackIso`.
* `det-sp-reduction-exceptional`: `reductionExceptional_isIso`,
  `reductionCtfCompactSupport`, `reductionCtfScalar`, and its specified counit
  equation in `Sheaf.SecSmoothPurity.ReductionExceptional`.
* `thm-cbc-finite-level-proetale`:
  `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange` reexports the general
  `globalFiniteLevelCompactSupportBaseChange` and adds `isIso_csAuxiliaryExchange`.
  The latter alone is a residue-DVR specialization; this delivery does not impose
  that specialization on A or B. The general theorem and the node's identification
  argument justify the invertibility of the actual constructed beta on Dctf.
* The canonical open factor is the recorded
  `AlgebraicGeometry.ProEtale.ordinaryOpenExtensionBaseChangeIso` in
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicDerivedEquivalence` and
  `openSquareDerivedPullbackModel` retain their published coordinate changes.
  The available proof-dependency modules are imported without `public`.

The five auxiliary declarations only express the maps, coordinate changes and
full-subcategory restrictions belonging to this node's statement. Each has real
definition data and a source/blueprint docstring, and each is listed in
`lean.declarations`. There is no missing independent notion and no new node.

Edge cases checked: identity coefficients (A = B and φ = id), identity base change,
empty schemes, zero complexes, the zero ring B, d = 0, and non-flat quotients such
as Z/ℓ² → Z/ℓ. None is excluded. The adjunction-counit equations fix the maps even
in the identity cases; replacing one comparison by a scalar automorphism no longer
satisfies its defining equation in general. The input categories still range over
all finite commutative ℓ-primary rings and all intrinsic Dctf complexes.

Searches retained from the saved packet and refreshed during repair:

* `msearch.py leanfinder 'base change commutes with extension of finite coefficients
  compact support and exceptional inverse image'`: eight generic algebraic tensor
  base-change / elliptic-curve results, no matching sheaf-theoretic statement.
* `msearch.py leansearch 'mixed coefficient geometric base change compact support
  exceptional inverse image'`: eight generic algebraic tensor / geometric
  base-change stability results, no exact statement.
* `msearch.py loogle 'CategoryTheory.mateEquiv_vcomp'`: the generic mate-composition
  lemma only; no mixed compact-support/exceptional statement.
* `msearch.py grep 'mixedBaseChange|mixed.base.change|compactSupport.*coefficient'
  CategoryTheory`: zero hits. The saved packet also queried Loogle for
  `reductionExceptional, finiteLevelProetale` (no hits).
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for `mixedBaseChange`, the item id,
  and the helper names found no existing exact declaration. The broader saved
  compact-support search led to the existing proper mate, ordinary open exchange
  and intrinsic realization APIs, all reused instead of redefined.

Validation: `scompile.py` compiled the complete file (about 25 seconds per pass).
The dry run caught the unscoped-heartbeat style warning; the option is now scoped
to `mixedBaseChange`. The final complete packet is checked through the prescribed
`deliver2.py --no-push`; every module retains its normal 60-second limit.

## Second reading by NH

This is the dispatcher's requested author self-check, not a claim of an independent
second worker. With the current node, its six proof steps, the blueprint statement,
the dependency declarations, and the saved file open, I found and repaired the
unspecified-map and ambient-adjoint mismatches described above. I reread the repaired
file against every hypothesis and both displayed identities as detailed in the
correspondence above. In particular the four right adjoints are now constrained by
actual adjunctions on Dctf, c/c' and eA/eB obey their own defining transpose equations,
and beta is the actual proper/open composite. The two scalar/pullback changes of
coordinates in each displayed identity have the correct directions. The only
postponed theorem is the node's own `mixedBaseChange`, with all six proof steps in
its docstring. No definition contains postponed data; all universes and variables
are explicitly bound and no Lean line exceeds 100 characters.
