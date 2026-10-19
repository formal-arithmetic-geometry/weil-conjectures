## Worker report

The module `Sheaf.RingTheory.UniversalInjectiveCheckStalks` states Stacks Algebra
Tag 05CL, conditions (1) ⇔ (4), exactly as the item. The only postponed proof is
`LinearMap.universally_injective_iff_localizedAtContractedPrime`. The auxiliary definition
`LinearMap.localizedAtContractedPrime` constructs the node's canonical map `u_q` as a
linear map over `R_p`; its data contains no sorry. It uses the existing
`LocalizedModule.map` and `LinearMap.restrictScalars` along the existing
`Localization.localRingHom`. This is a helper for the already introduced localized map,
not a separate definition of universal injectivity or localization. Both declarations
are listed in the node's `lean.declarations`.

Clause-by-clause comparison with the node and with the source `algebra.tex`,
`lemma-universally-injective-check-stalks` (lines 20106–20170):

- The commutative ring map `R → A` is `[CommRing R] [CommRing A] [Algebra R A]`,
  with its homomorphism `algebraMap R A`. Every commutative ring homomorphism gives
  such an algebra structure; it need not be injective or flat.
- The modules `M`, `M'` are `M : Type w`, `N : Type x`, with `AddCommGroup` and
  `Module A` structures. The compatible `Module R` and `IsScalarTower R A` binders
  express restriction along the specified map. They impose no extra property of the
  modules: these structures exist canonically by `Module.compHom`.
- The A-linear map `u` is `f : M →ₗ[A] N`.
- The point `q ∈ Spec(A)` is `q : PrimeSpectrum A`, the underlying set of the
  recorded `AlgebraicGeometry.Spec`. Its prime ideal is `q.asIdeal`.
- The contraction `p = q ∩ R` is the literal ideal
  `q.asIdeal.comap (algebraMap R A)`; no independent prime or equality assumption is added.
- The modules `M_q`, `M'_q` are the recorded fraction modules
  `LocalizedModule q.asIdeal.primeCompl M` and its counterpart for `N`.
- The map `u_q` is `f.localizedAtContractedPrime (R := R) q`. Its underlying function
  is `LocalizedModule.map q.asIdeal.primeCompl f`, so fractions map as `m/s ↦ f(m)/s`.
- The scalar ring on the right is exactly `Localization.AtPrime p`, not R or A_q.
  Its actions on both fraction modules are explicitly `Module.compHom` along
  `Localization.localRingHom p q.asIdeal (algebraMap R A) rfl`. These are the canonical
  actions induced by `R_p → A_q`. The helper installs the algebra and scalar towers
  by existing constructors, and then restricts the A_q-linear fraction map.
- Universal injectivity on the left is written out as
  `∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L],
  Function.Injective ((f.restrictScalars R).lTensor L)`.
  `LinearMap.lTensor` is the map `1_L ⊗ f`, exactly the node's `L ⊗_R u`.
- Universal injectivity at each q is the same quantification, with
  `[Module (Localization.AtPrime p) L]` and `LinearMap.lTensor` over `R_p` applied
  to the canonical helper map. The two explicit `Module.compHom` arguments to
  `@LinearMap.lTensor` ensure that the tensor products use these canonical actions.
- The connective `↔` is the stated if and only if. All primes are quantified, and
  there is no finite-generation, flatness, nontriviality, or nonzero-module assumption.
- R, A, M and N have independent universes u, v, w, x. The test modules have universe
  `max u v w x y`, where y is also explicit. In particular the test universe is never
  below the base ring and allows the localization and tensor witnesses in the proof.
  This is the usual universe-polymorphic encoding of quantification over modules;
  increasing y permits arbitrarily large modules without identifying object universes.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`, `LocalizedModule.mk`, `LocalizedModule.mkLinearMap`; its induced
  localized map is `LocalizedModule.map` in `Mathlib.RingTheory.Localization.Module`.
  The latter is already linear over `Localization q.asIdeal.primeCompl`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; its underlying prime set
  is `PrimeSpectrum A`, with contraction `Ideal.comap`.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  and `Module.Flat` in `Mathlib.RingTheory.Flat.Basic`. The node cites this definition
  but states no flatness hypothesis or conclusion; its import is retained as the
  recorded statement dependency. In particular no flatness condition was added.
- The helper additionally uses `Localization.localRingHom` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and the ordinary
  `Module.compHom`, `IsScalarTower.of_compHom`, and `LinearMap.restrictScalars`.

All available proof dependencies are imported without `public`:
`bijective_of_localized_maximal` (`Mathlib.RingTheory.LocalProperties.Exactness`),
`LocalizedModule.map_exact` (`Mathlib.Algebra.Module.LocalizedModule.Exact`),
`IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor`, together with
`IsLocalization.moduleTensorEquiv` and the tensor localization instance
(`Mathlib.RingTheory.Localization.BaseChange`). Their full source signatures were read.
The docstring explains the tensor comparisons, their compatibility with f, the kernel
argument at maximal ideals, and the converse using any R_p-module. Its use of right-tensor
comparisons is reconciled with the statement's left tensors by tensor symmetry.

Edge cases checked before finalizing:

- A is the zero ring: its spectrum is empty and every unital A-module is zero, so both
  sides are true. No nontriviality instance excludes this case. R zero forces A zero.
- f is an identity: every tensor and localization is an identity. Zero modules also work.
- f is zero: the left side forces M zero (take L = R, lifted as necessary), and the
  right side forces each M_q zero, which detects the same condition.
- Multiplication by 2 on Z is injective but fails universal injectivity after tensoring
  with Z/2; the right side fails at q = (2). Thus ordinary injectivity was not substituted.
- Z → Q as a Z-linear module map also fails after tensoring with Z/2, and fails the
  corresponding local test. Conversely arbitrary identities over the nonflat algebra
  Z → Z/2 are included: the map of rings need not be flat.

Searches for existing declarations:

- `msearch.py leanfinder`, query “A linear map is universally injective over a base ring
  if and only if its localizations at all primes of the algebra are universally injective
  over the localized base ring”: eight hits, including
  `IsLocalization.mapₐ_injective_of_injective` and `injective_of_localized_maximal`;
  none states universal tensor injectivity over the contracted local base.
- `msearch.py loogle`, query `LocalizedModule.map, Function.Injective`: four hits,
  including `LocalizedModule.map_injective` and `injective_of_localized_maximal`;
  these concern injectivity of one map, not injectivity after every tensor product.
- `msearch.py leansearch`, query “universally injective module linear map tensor
  localization prime stalks”: eight hits including stalk comparisons and
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective`; none is the criterion.
- `msearch.py grep`, query
  `universally.injective|universallyInjective|UniversallyInjective` in Mathlib/RingTheory:
  zero hits. Direct rg of Mathlib/RingTheory and LinearAlgebra returned only unrelated
  purely inseparable results for the broader `IsPure` pattern.
- Direct rg of upstream `WeilConjectures` for the item id returned zero hits; searches
  for universally injective found scheme-morphism statements, not this module criterion.
- Direct rg of `lean/Sheaf/RingTheory` found the consumer `FreeSubtractionFlatness.lean`
  and an unrelated reference in `FiniteGabberPolynomial.lean`. The consumer cites this
  criterion in its proof docstring but does not state it. Other Sheaf matches concern
  scheme morphisms or purely inseparable fields. The exact new declaration names were
  also searched across Mathlib, upstream WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`, with no existing declaration.

No node statement was corrected, no new node is required, and no dependency record is
changed. The redundant flatness definition citation was left intact as required.

Validation uses only the prescribed scompile.py and deliver2.py wrappers. The first
elaboration diagnosed the missing inferred local scalar instance in `.lTensor`; explicit
instance arguments repaired it without any extra mathematical hypothesis. No result is
proved at this stage; the theorem's whole proof is `sorry`.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
