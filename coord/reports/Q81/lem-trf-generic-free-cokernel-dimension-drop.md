## Worker report

The module `Sheaf.TraceFormula.GenericFreeCokernelDimensionDrop` states
`RingHom.generic_free_cokernel_dimension_drop`, with `sorry` as its entire proof.
It defines no new notions, introduces no new nodes, and changes only `lean` on the
assigned node. There is no repair note for this item. No statement correction or
STATEMENT-DISPUTED flag is needed.

Source read: `literature/stacks-project/flat.tex`, Tag 05I3,
`lemma-induction-step` (existence and (1) implies (2)), and Tag 05I5,
`proposition-finite-type-flat-at-point`, first proof, induction step. Tag 05I3
assumes a flat finitely presented map with geometrically integral fibres; the
selected generic basis gives a universally injective map and localized flat
cokernel. Tag 05I5 uses the cokernel's support missing the generic point to obtain
the strict dimension drop. The node's more explicit prescribed-generators,
universal exactness and zero-dimensional clauses follow its six proof steps,
which are reproduced in the theorem docstring.

Hypotheses, individually:

- The commutative local base is `{A : Type u} [CommRing A] [IsLocalRing A]`;
  its maximal ideal is `IsLocalRing.maximalIdeal A`. The commutative algebra is
  `{B : Type v} [CommRing B] [Algebra A B]`, with map `algebraMap A B`.
- Flatness is `hflat : RingHom.Flat (algebraMap A B)`. Finite presentation is
  `hfp : Algebra.FinitePresentation A B`. No smoothness or Noetherian hypothesis
  is added.
- `hgeom` quantifies over every `a : PrimeSpectrum A` and every field `K`
  extending `a.asIdeal.ResidueField`, with its compatible A-action expressed by
  `algebraMap A K = ι.comp (algebraMap A a.asIdeal.ResidueField)`. The required
  nonzero domain is `IsDomain (K ⊗[A] B)`, canonically the extension to K of
  the fibre at a. This is exactly the interface of the existing generic-basis
  dependency. Its `geometricFibres_domain_baseChange` transports this condition
  from `Type (max u v w)` to arbitrary universes, including the identity field
  extension; the field quantifier is not vacuous or restricted below A or B.
- The finite closed-fibre dimension is `n : ℕ` and `hdim`, the equality of
  `topologicalKrullDim (PrimeSpectrum (B ⧸ mB))` with `(n : WithBot ℕ∞)`.
  Here and throughout `mB` is literally
  `Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)`.
- The prime q is `q : PrimeSpectrum B`, and lying over m is exactly
  `hq : q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A`.
- The finite B-module is `(N : Type t) [AddCommGroup N] [Module B N]
  [Module.Finite B N]`. `[Module A N] [IsScalarTower A B N]` provide its unique
  compatible restricted A-action and add no mathematical condition on N.
- `hNq` is `Module.Flat A (LocalizedModule q.asIdeal.primeCompl N)` with
  the A-module structure explicitly `Module.compHom ... (algebraMap A B)`.
  Thus only N localized at q is assumed flat over A, not N over B or globally
  over A.

Conclusions, individually:

- `∃ hp : (Ideal.map ... (IsLocalRing.maximalIdeal A)).IsPrime` asserts primality
  of p = mB. The proof witness hp then supplies the prime instance to the actual
  `Ideal.ResidueField`; primality is a conclusion, not an added hypothesis.
- For every specified finite list `(s : ℕ) (x : Fin s → N)` satisfying
  `Submodule.span B (Set.range x) = ⊤`, the theorem supplies `r : ℕ` and
  `α : (Fin r → B) →ₗ[B] N`. Finite functions are the finite direct sum B^r.
  `j : Fin r ↪ Fin s` and `∀ i, α (Pi.single i 1) = x (j i)` say that the
  standard basis maps to selected members of that very list. Distinct indices
  do not strengthen the mathematical content: repeated selected images would
  contradict the generic isomorphism over the nonzero residue field. Rank zero
  is allowed, and no nonemptiness assumption is imposed on either index set.
- `Function.Bijective (LinearMap.lTensor (@Ideal.ResidueField B _ p hp) α)`
  is the residue-field isomorphism. Tensor symmetry identifies the left-tensor
  form with the node's alpha tensor kappa(p); a bijective linear map is exactly
  a linear isomorphism, not merely injective or surjective.
- Q is literally `N ⧸ LinearMap.range α`; `Module.Finite B` on this quotient
  asserts finiteness of the cokernel. No arbitrary replacement module is used.
- The quantifier over `(L : Type z) [AddCommGroup L] [Module A L]` asserts
  `Function.Injective (LinearMap.lTensor L (α.restrictScalars A))`. The universe
  z is independent of the base, algebra and N, as in the dependency interface.
  This is precisely A-universal injectivity, and includes injectivity of alpha
  by taking L = A.
- `Module.Flat A (LocalizedModule q.asIdeal.primeCompl (N ⧸ range α))`, again
  with explicit restricted action, asserts A-flatness of Q_q.
- For every `(A' : Type y) [CommRing A'] [Algebra A A']`, the three clauses
  `Function.Injective`, `Function.Exact` and `Function.Surjective` express the
  short exact sequence obtained by left-tensoring alpha and the actual quotient
  map `(LinearMap.range α).mkQ` over A. The middle and final maps are canonical.
  The independent universe y includes arbitrary algebra base changes. No
  flatness of A' is assumed. Taking A' = A also recovers the original sequence.
- The witness Z is constrained by equality to
  `Module.support (B ⧸ mB) ((B ⧸ mB) ⊗[B] (N ⧸ range α))`.
  Tensoring with the quotient algebra is the canonical realization of Q/mQ.
  Mathlib's `Module.support` is the set of primes with nontrivial localized
  module, exactly the node's set. Z cannot be chosen freely to satisfy the
  later dimension clauses.
- `IsClosed Z ∧ Z ≠ Set.univ` asserts that this support is closed and proper
  in the integral closed fibre. Primality hp already expresses that the
  quotient B/mB is a nonzero integral domain.
- For every closed-fibre point ξ whose comap along `Ideal.Quotient.mk mB` is
  `⟨mB, hp⟩`, the theorem asserts `ξ ∉ Z`. The quotient-map spectrum bijection
  identifies this unique point with the zero prime of B/mB, namely the generic
  point. This avoids introducing either an arbitrary prime or a further
  hypothesis that the zero ideal is prime.
- `Z.Nonempty → topologicalKrullDim Z < (n : WithBot ℕ∞)` is the strict global
  dimension drop for nonempty support. The subtype Z carries its subspace
  topology, so the dimension is the dimension of the support itself.
- `∀ ξ : Z, PrimeSpectrum.comap (Ideal.Quotient.mk mB) ξ.val = q →
  topologicalKrullDimAt ξ < (n : WithBot ℕ∞)` is the dimension drop at q
  whenever q belongs to the support, using the same quotient-map correspondence.
  The local dimension is taken within Z, not within the entire closed fibre.
- `n = 0 → Z = ∅` explicitly includes the zero-dimensional conclusion.

Dependency declarations used (their recorded signatures and docstrings were read):

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`;
  `topologicalKrullDim` is the Mathlib definition imported by this module.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`; its underlying
  space is Mathlib's `PrimeSpectrum`, used directly for these affine supports.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the affine residue field is the existing
  `Ideal.ResidueField`, identified by `Scheme.Spec.residueFieldIso`. No private
  version of residue fields is introduced.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`: `TensorProduct` and
  `LinearMap.lTensor`, publicly supplied by the imported tensor-product modules.
- `Sheaf.TraceFormula.LocalGenericBasisUniversalInjective`:
  `RingHom.geometricFibres_domain_baseChange`,
  `RingHom.maximalIdeal_map_isPrime_of_geometricFibres`, and
  `RingHom.local_generic_basis_universal_injective` (proof-only import).
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`: `lTensor_exact`,
  `rTensor_exact` (proof-only import).
- `Mathlib.RingTheory.Support`: `Module.mem_support_iff_of_finite`,
  `Module.support_eq_zeroLocus`; this import is public since `Module.support`
  itself is used in the statement.
- `WeilConjectures.Topology.IrreducibleOpenComplementDimension`:
  `irreducible_open_complement_dimension` (proof-only import).

Edge cases checked before writing: N = 0 permits r = 0 and empty support; the
empty prescribed generating list forces N = 0 and admits the empty embedding.
For A = k, B = k[t] and N = B/(t), the generic fibre module is zero, r = 0,
and the support is a closed point of dimension 0 < 1. For N = B the quotient
is zero. For B = A and N finite flat, n = 0 gives a free basis and empty
cokernel support. No trivial ring can satisfy a geometrically integral nonzero
closed fibre (and q over the maximal ideal supplies a point); this is not an
additional assumption. No characteristic restriction, Noetherianity, positive
rank, positive dimension or nonempty support is imposed.

Searches made in this session:

- `msearch.py ... leanfinder "generic free submodule with flat cokernel and
  smaller closed fibre support dimension"`: eight hits, including
  `Module.freeLocus_eq_univ`, `Module.free_of_flat_of_finrank_eq`,
  `Module.nonempty_basis_of_flat_of_finrank_eq`, `Module.supportDim` and its
  inequalities. These require flatness over the module ring or concern other
  support inequalities; none states this result over a local base.
- `msearch.py ... loogle "Module.Flat, Module.Finite, Ideal.IsPrime"`: twelve
  hits, principally `Module.rankAtStalk_eq_of_le_of_finite_of_flat'`,
  `Ideal.finrank_fiber_eq_rankAtStalk`, and ramification formulas. None constructs
  this submodule and controls the localized flat cokernel and support dimension.
- `msearch.py ... grep "generic.*basis|cokernel.*flat|support.*[dD]im"
  RingTheory`: ten hits in KrullDimension/Regular and KrullDimension/Module;
  individual support-dimension facts only.
- `rg -n "generic.*(basis|free)|cokernel.*(dim|support)|dimension_drop"`
  in both `lean/WeilConjectures` and `lean/Sheaf`: hits include the existing
  local generic-basis criterion and coherent-sheaf generic construction modules,
  with different hypotheses and conclusions. No exact existing statement.
- `grep -rn "lem-trf-generic-free-cokernel-dimension-drop"` in
  `lean/WeilConjectures`: no hits.
- Full-name `rg` for `generic_free_cokernel_dimension_drop` in
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and `Sheaf`:
  no existing declaration.

Validation: the prescribed `scompile.py Q81` invocation compiled this file as
both sandbox and final library module, with exit code 0, in approximately two
seconds per pass, without errors or warnings. The final delivery dry run is
run separately through `deliver2.py --no-push`.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
