## Worker report

The module `Sheaf.RingTheory.KoszulPolynomialPresentationIndependence` states
`Algebra.koszulRegular_kernel_of_polynomial_presentation`, with `sorry` as its
only proof. It states independence of the finite polynomial presentation for the
primewise local Koszul-regular kernel condition. The condition is expanded in
both hypothesis and conclusion, as in the neighboring syntomic-kernel and
faithfully-flat-descent statements. No definition, helper theorem, new node,
dependency repair or statement correction is needed. Only `lean` changes in the
item's node copy.

Clause-by-clause correspondence:

- Commutative rings R and S, with their specified R-algebra structure:
  `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]`.
  The two ring universes are independent.
- Finite polynomial presentations with n,m >= 0: `(n m : ℕ)` and
  `MvPolynomial (Fin n) R`, `MvPolynomial (Fin m) R`.
- The specified R-algebra maps alpha and beta are the binders `α` and `β` of
  type `... →ₐ[R] S`; their surjectivity is `hα : Function.Surjective α` and
  `hβ : Function.Surjective β`.
- The kernel of either map is `RingHom.ker ...toRingHom`.
- The introductory local condition for an ideal L in T is rendered explicitly
  by `∀ p : Ideal T, p.IsPrime → L ≤ p → ...`. Thus exactly the primes
  containing L are tested, without a global finite-generation hypothesis.
- A principal neighborhood outside p is `∃ u : T, u ∉ p ∧ ...`.
- Its ring T_u is the recorded construction `Localization.Away u`.
- The allowed length and generators are `∃ (r : ℕ) (a : Fin r → Localization.Away u)`.
  Each prime chooses its own u, r and a.
- The equality L T_u = (a_1,...,a_r) is
  `L.map (algebraMap T (Localization.Away u)) = Ideal.span (Set.range a)`.
- Vanishing of every positive Koszul homology group is
  `RingTheory.Sequence.IsKoszulRegular a`. Its actual definition is
  `∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex _ r a).homology i)`;
  over natural degrees `i ≠ 0` is precisely `i > 0`.
- The assumption on ker alpha is `hlocal` with that whole condition. The
  theorem's conclusion is exactly the same condition for ker beta.
- No flatness, Noetherianity, finite presentation of S or nontriviality binder
  occurs. The finite-type condition in Stacks 07CZ already follows from either
  displayed surjective finite-variable presentation and is not added as an
  independent hypothesis.

Dependency declarations read and used in the statement:

- `def-weil-ring-localization-away`: `Localization.Away` in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with its ring/algebra structure
  exposed by `Mathlib.RingTheory.Localization.Away.Basic`. This is the actual
  localization at the submonoid of powers; the structure map is `algebraMap`.
- `def-weil-pbc-koszul-regular-sequence`:
  `RingTheory.Sequence.IsKoszulRegular` in
  `WeilConjectures.RingTheory.KoszulRegularSequence`. Its full definition and
  docstring were read; the other three predicates in the node are not substituted
  for ring-valued Koszul regularity.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`. Its recorded `aeval` and `algHom_ext`
  signatures/docstrings were also read; they provide the graph-evaluation proof
  interface rather than an alternate definition of a polynomial ring.

Stated proof dependencies are plain imports, as required: the upstream modules
`RegularSequenceKoszulRegular`, `KoszulConormalBasis`,
`ConormalModulePrincipalLocalization`, `KoszulRegularFlatBaseChange`, and Mathlib's
`Localization.AtPrime.Basic`, `LocalRing.Module`, `Flat.Localization` (all under
`RingTheory`). They give the recorded weak-regular implication, conormal basis,
stable conormal isomorphism, flat-base-change theorem, prime localization,
Nakayama and flatness of localization. The prefix-quotient criterion and
equal-length-generators nodes currently have no Lean record or Mathlib match;
they are not needed for this signature, are not restated, and remain explicit
references in the complete eight-step proof docstring.

Sources and edge cases checked before writing:

- Read `literature/stacks-project/more-algebra.tex`, Tag 07CZ, statement and full
  graph-presentation proof. The accepted node supplies the primewise refinement
  avoiding an unwarranted global finite-generation assumption.
- For S = 0 both kernels are the unit ideal, so there are no primes containing
  either kernel. The universal conditions are vacuous, correctly, and there is
  no `[Nontrivial S]` assumption.
- n = 0 or m = 0 is permitted by `Fin 0`; these are polynomial presentations
  with no variables, with no positivity assumption.
- r = 0 is permitted independently on every chart. The span of its empty range
  is the zero ideal, and its positive Koszul homology vanishes. In particular,
  the zero ideal is locally regular using u = 1 and the empty sequence.
- The zero base ring is allowed; a unital R-algebra over it is also zero.
- No global bound on r or globally finite kernel is asserted. Neither
  commutative ring universe is tied to the other.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder "Local Koszul regularity of kernels is independent
  of the finite polynomial presentation of an algebra"`: eight hits, including
  `Algebra.SubmersivePresentation.isStandardSmooth`, `Algebra.IsStandardSmooth`
  and smooth/local-regular results; none states kernel Koszul presentation
  independence.
- `msearch.py ... loogle "MvPolynomial, RingHom.ker"`: twelve hits, including
  `MvPolynomial.ker_map`, `ker_mapAlgHom`, finite-presentation kernel finite
  generation, and presentation kernel identities; none states this theorem.
- `msearch.py ... grep "[Kk]oszul|[Ll]ocally[Kk]oszul" RingTheory`: one Mathlib hit,
  the TODO about Koszul regular sequences in `Regular/RegularSequence.lean`.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for local Koszul predicate
  names and Koszul/presentation combinations, and the exact node id: found the
  syntomic kernel consumer's proof reference, conormal presentation modules and
  unrelated Koszul tower constructions, but no declaration of this theorem.
- `rg` over `dag/nodes` and both RingTheory directories for
  `IsLocallyKoszul|LocallyKoszul|locally[Kk]oszul|locally_koszul`: the landed
  faithfully-flat-descent and conormal-intersection statements expand the same
  condition inline; there is no duplicate predicate to import.
- `rg` in `dag/lean_names_upstream.json` for Koszul/presentation combinations:
  no recorded exact match.

No statement dispute or node fault was found. The introductory local condition
is written explicitly, not replaced by a Noetherian local or globally generated
variant. Every variable and universe is bound, with `autoImplicit false` enabled.

Validation: the required server single-file compile and delivery dry run are
recorded by the prescribed wrappers. Only the expected sorry warning is allowed.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
