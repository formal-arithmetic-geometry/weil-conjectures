## Worker report

The module states `MvPolynomial.homogeneous_primary_decomposition`, with its only proof
postponed by `sorry`. No definitions, dependency repairs, new nodes, or statement corrections
are introduced. The accepted stage-1 split is preserved. The previous worker's stage-1
live-wins objection does not apply: the node has no Lean record and the current queue assigns
stage 2. No released repair note for this item was present.

Clause-by-clause reading:

- The arbitrary field is `(k : Type u) [Field k]`, with an explicitly declared universe `u`.
- `n : ℕ` includes n = 0; `MvPolynomial (Fin (n + 1)) k` is exactly k[x_0,...,x_n].
- `I : Ideal ...` and `hI : @Ideal.IsHomogeneous ... gradedAlgebra I` assert closure under
  the components of the fixed total-degree grading. The explicit instance argument is
  Mathlib's canonical `MvPolynomial.gradedAlgebra`, not a further grading hypothesis.
- `IsNoetherianRing ...` is the first conclusion, not an added hypothesis. It means every
  ideal is finitely generated.
- `∃ (s : ℕ) (Q : Fin s → Ideal ...)` gives the finite family and allows s = 0.
- `I = ⨅ a, Q a` is the intersection equality, including the empty intersection.
- `∀ a, Q a ≠ ⊤ ∧ ...` states properness and, with `Ideal.IsHomogeneous`, homogeneity of
  each primary component. `(Q a).IsPrimary` is Mathlib's existing primary predicate.
  `Ideal.isPrimary_iff` states exactly the proper-ideal/power condition of the node:
  uv ∈ Q and u ∉ Q force v into the radical, hence some positive power into Q.
  A zero exponent cannot witness membership in a proper ideal.
- `(Q a).radical` is exactly p_a. Its conjuncts `.IsPrime` and `Ideal.IsHomogeneous`
  assert that these are homogeneous prime ideals. Mathlib radical membership permits
  exponent zero; in that case Q = top and exponent one also works, so its radical is
  exactly the node's positive-power radical.
- `Function.Injective (fun a => (Q a).radical)` states distinctness of the radicals.
- `∀ a, (⨅ (b : Fin s) (_ : b ≠ a), Q b) ≠ I` says deleting any single component changes
  the intersection, exactly irredundancy for a finite family already intersecting to I.
- `∀ p ∈ I.minimalPrimes, ∃ a, (Q a).radical = p` gives every minimal prime over I.
- `∀ a, ∃ h : ℕ, 1 ≤ h ∧ (Q a).radical ^ h ≤ Q a` gives every positive radical-power bound.
- `∀ (p : Ideal ...) [p.IsPrime], I ≤ p → ...` quantifies over every prime containing I.
  The typeclass binder is universal quantification over a proof of primality, not a
  restriction on the decomposition. The chosen Q is outside this quantifier.
- `I.map (algebraMap _ (Localization.AtPrime p))` is extension IB_p along the canonical
  localization ring map. Its equality with the doubly indexed infimum over a and proofs
  of `(Q a).radical ≤ p` is the specified surviving-factor localization formula.
- `∀ a, ¬ (Q a).radical ≤ p → ... = ⊤` is precisely the unit-factor assertion for every
  excluded radical.
- `∀ b, p = (Q b).radical → I.IsMinimalPrime p → ...` gives equality of IB_p with Q_bB_p
  at each minimal prime radical. Using the already quantified prime p avoids any choice
  of a new prime structure or an arbitrary localization.
- For I = top, s = 0 makes the infimum top, every component assertion vacuous, and there
  is no prime containing I. Thus the empty-family clause is retained without an extra
  redundant conjunct. Conversely properness prevents a nonempty decomposition of top.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, lines 170--180.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, Mathlib.Algebra.MvPolynomial.Basic:82;
  evaluation `MvPolynomial.aeval`, Eval:593; uniqueness `MvPolynomial.algHom_ext`, Basic:436.
  The universal-property clauses need no additional theorem in this statement.
- `def-pc-standard-graded-algebra`: imported
  WeilConjectures.RingTheory.GradedAlgebra.Standard; read `GradedAlgebra.IsStandard`
  and its degree-zero and generation discussion. No arbitrary standard graded algebra
  or standardness hypothesis is introduced because this node fixes the polynomial ring.
  The associated homogeneous-ideal notion is Mathlib's `Ideal.IsHomogeneous`,
  Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal:60--66. The canonical polynomial
  grading and its component identification are in
  Mathlib.RingTheory.MvPolynomial.Homogeneous:602--642 (`gradedAlgebra`, `decomposition`,
  and `decomposition.decompose'_apply`). The explicit grading instance supplies that
  existing notion without a file-local instance or a replacement definition.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  Mathlib.RingTheory.Localization.AtPrime.Basic:53--58; the statement uses its canonical
  `algebraMap`. Residue fields and fibre rings are not needed by the item's statement.
- Existing auxiliary notions are `Ideal.IsPrimary` and `Ideal.isPrimary_iff` in
  Mathlib.RingTheory.Ideal.IsPrimary:33--43, `Ideal.radical`, `Ideal.IsPrime`, and
  `Ideal.minimalPrimes` / `Ideal.IsMinimalPrime` in
  Mathlib.RingTheory.Ideal.MinimalPrime.Basic:39--58. No private copies are made.

Proof imports follow the recorded plan: Mathlib.RingTheory.Lasker
(`Submodule.isLasker`), Mathlib.RingTheory.GradedAlgebra.Radical
(`Ideal.IsHomogeneous.radical`), Mathlib.RingTheory.Finiteness.Ideal
(`Ideal.exists_pow_le_of_le_radical_of_fg`), and
Mathlib.RingTheory.RegularLocalRing.Polynomial
(`MvPolynomial.isRegularRing_of_isRegularRing`). `lem-sfb-primary-homogeneous-core` has
no recorded Lean declaration or usable module yet; its import is omitted and its role
is retained explicitly in the ten-step proof docstring. It is only a proof dependency;
no part of the present statement needs its theorem or a new interface.

Edge cases checked mathematically: I = top uses the empty family; I = 0 uses the zero
prime in the polynomial domain; n = 0 still has one variable, as specified; finite and
positive-characteristic fields introduce no restrictions; a singleton decomposition has
top as the intersection after deletion. For embedded components, in k[x,y] the example
(x²,xy) = (x) ∩ (x²,y) has radicals (x) and (x,y). Localizing at (x) discards the second
factor while at (x,y) both survive. Thus the localization condition does not inadvertently
require every radical to be minimal, and the last clause applies only at minimal primes.
All universes and variables are explicitly bound; `set_option autoImplicit false` is not
needed to introduce any hidden binder.

Source checked online: Altman--Kleiman,
[A Term of Commutative Algebra](https://web.mit.edu/18.705/www/13Ed.pdf),
Theorem 20.27 and Exercises 20.25--20.26 on printed pp.122--123, Proposition 18.24 and
Theorem 18.25 on printed pp.109--110. They support homogeneous primary factors and the
localization clauses. No statement fault or STATEMENT-DISPUTED issue was found.

Searches performed, with actual logged outputs in searches.jsonl:

- grep: `homogeneous.*[Pp]rimary|[Pp]rimary.*homogeneous|primary.*[Dd]ecomposition` in RingTheory; 7 hits. Candidates: Mathlib/RingTheory/Lasker.lean, Mathlib/RingTheory/Lasker.lean, Mathlib/RingTheory/Lasker.lean, Mathlib/RingTheory/Lasker.lean. None states the complete graded decomposition with localization data.

- loogle: `"IsHomogeneous", "IsPrimary"`; 0 hits. No declaration combines the requested predicates.

- leanfinder: `Every homogeneous ideal of a polynomial ring over a field admits a finite irredundant homogeneous primary decomposition with distinct radicals and localization at primes`; 8 hits. Candidates: Ideal.IsHomogeneous.radical_eq, AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime, Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem, AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.relevant. None states the complete graded decomposition with localization data.

- leansearch: `A homogeneous ideal in a polynomial ring over a field has a finite homogeneous primary decomposition with distinct radicals and localization at any prime`; 8 hits. Candidates: Ideal.isPrimary_decomposition_pairwise_ne_radical, Ideal.IsMinimalPrimaryDecomposition.distinct, Ideal.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition, Ideal.IsHomogeneous. None states the complete graded decomposition with localization data.

Additional direct `rg` searches of lean/WeilConjectures and lean/Sheaf for
`homogeneous.*[Pp]rimary|[Pp]rimary.*homogeneous|lem-sfb-homogeneous-primary-decomposition`
returned no matching theorem. A separate search for `homogeneous_primary_decomposition`
returned no existing declaration. Ordinary minimal primary decomposition in Lasker.lean
was read, but does not supply homogeneous primary factors.

Validation: the delivered module compiled on the server through scompile.py with no
errors or warnings. A preceding module-mode type probe found the exact explicit-instance
signature of `Ideal.IsHomogeneous`; its unrelated exploratory lookup of the unimported
`Ideal.IsMinimalPrimaryDecomposition` was removed from the delivery. No local or global
build was run. The module contains only one postponed theorem and no diagnostic commands.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
