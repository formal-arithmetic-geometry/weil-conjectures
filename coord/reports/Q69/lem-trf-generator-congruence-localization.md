## Worker report

Item: lem-trf-generator-congruence-localization. The module
`Sheaf.RingTheory.GeneratorCongruenceLocalization` states
`RingHom.exists_unique_generator_congruence_localization`, with its sole proof `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement corrections.
Only the item's `lean` record changes.

Source read: `literature/stacks-project/more-morphisms.tex`, lemma-map-approximation,
Tag 0CAU, especially the polynomial presentation, the equations and congruences for the b_i,
the sentence determining the R-algebra map B to A', and the final marked-point assertion.
The module docstring expands all seven proof steps of the node, including the residue-field
argument that the source leaves implicit.

Hypotheses and objects, clause by clause:

- R, A, A' are `{R : Type u} {A : Type v} {A' : Type w}`, each with `CommRing`,
  and `[Algebra R A] [Algebra R A']`. Their universes are independent.
- Noetherianity of both algebras is exactly `[IsNoetherianRing A] [IsNoetherianRing A']`.
  There is no Noetherianity assumption on R.
- The map h is `(h : A →ₐ[R] A')`. The prime ideals are `(p : Ideal A)` and
  `(p' : Ideal A')`, with `[p.IsPrime] [p'.IsPrime]`.
- The inverse-image condition is `hp : Ideal.comap h.toRingHom p' = p`.
  `Localization.localRingHom p p' h.toRingHom hp.symm` is the specified induced local map.
- Its completed map is the same `Classical.choose
  (RingHom.exists_adicCompletion_map_of_local (...))` everywhere in the statement.
  This chooses a map with the recorded coordinate characterization, not an unconstrained
  ring homomorphism. Each coordinate of an element has a representative in the original
  ring; the characterization prescribes its image at every coordinate. Since completion
  elements are compatible sequences, it uniquely determines this map. The upstream theorem
  has a proved construction; there is no new postponed data or assumption here.
- The finite integers n and m are arbitrary `(n m : ℕ)`. The polynomials are
  `F : Fin m → MvPolynomial (Fin n) R`, with B literally the quotient
  `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range F)`. This is the finite-variable polynomial
  ring from the node's proof dependency def-weil-pbc-mv-polynomial-ring. Its finite monomials
  are the same as in the iterated univariate polynomial ring specified in the statement;
  choosing the standard multivariate representation changes neither the generators, the
  relations, nor the algebra. No alternate polynomial-ring definition is introduced.
- The marked prime is `q : Ideal (...)` with `[q.IsPrime]` on this actual quotient B.
- The map theta is `θ : Localization.AtPrime q →ₐ[R] AdicCompletion ...`, with completion
  ideal `IsLocalRing.maximalIdeal (Localization.AtPrime p)` and `[IsLocalHom θ]`.
  Both rings are local: the completion instance follows from Noetherianity of the
  localization. For maps of local rings, `IsLocalHom` (reflecting units) is equivalent
  to the asserted inverse-image equality of maximal ideals.
- N is `(N : ℕ)` with `hN : 1 ≤ N`; the proposed values are `b : Fin n → A'`.
- The equations are `hF : ∀ j : Fin m, MvPolynomial.aeval b (F j) = 0`.
- In `hb`, the element a_i is written out as theta applied to the localization image
  of `Ideal.Quotient.mk ... (MvPolynomial.X i)`. The other term is b_i mapped first
  to `Localization.AtPrime p'` and then to its completion. The ideal J is exactly
  `Ideal.map (algebraMap (Localization.AtPrime p') (AdicCompletion ...))
  ((IsLocalRing.maximalIdeal (Localization.AtPrime p')) ^ N)`. This is the extension
  of the N-th power, not a replacement by an unverified kernel or an extra condition.

Conclusions, clause by clause:

- `∃ φ : B →ₐ[R] A', ...` supplies an R-algebra map and the first conjunct gives
  `∀ i, φ (Ideal.Quotient.mk ... (MvPolynomial.X i)) = b i`.
- The next conjunct quantifies over EVERY R-algebra map `ψ : B →ₐ[R] A'` and states
  that these same generator equalities alone imply `ψ = φ`. Thus uniqueness is for
  the prescribed generator values, independently of the additional conclusions.
- The next conjunct quantifies over every `H : MvPolynomial (Fin n) R` and states
  the required completed difference is in exactly the same J. Both occurrences of H
  pass through the identical quotient map. The first passes through theta and the
  completed map of h, and the second through phi, localization, and completion.
- `∃ hφ : q = Ideal.comap φ.toRingHom p', ...` asserts precisely the inverse-image
  prime equality, with its orientation chosen for Mathlib's canonical localization API.
- `Localization.localAlgHom q p' φ hφ` is the induced R-algebra map on localizations.
  The next conjunct explicitly asserts `IsLocalHom` for that very map.
- The final `∀ z : Localization.AtPrime q` asserts the completed congruence in J on
  ALL fractions, using that canonical localAlgHom, not an arbitrary local map.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`
  and its ideal-finiteness characterization.
- def-weil-pbc-localization-at-prime: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`; also its `Localization.localRingHom` and
  `Localization.localAlgHom`, with their full signatures and locality API read.
- def-weil-pbc-adic-completion: `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`;
  its ring and base-algebra structures and coordinate maps are in
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- def-weil-polynomial-ring: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`. That module
  is explicitly imported; finite iteration is represented by the existing multivariate
  ring already named in the node's proof. No private copy is used.
- lem-weil-pbc-fs-adic-completion-map-local:
  `WeilConjectures.RingTheory.CompletionMapForLocalHom`,
  `RingHom.exists_adicCompletion_map_of_local`; its full coordinate characterization
  and its proved quotient-by-quotient construction were read.
- Proof dependency def-weil-pbc-mv-polynomial-ring: `Mathlib.Algebra.MvPolynomial.Basic`
  and `.Eval`, `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`.
- Proof dependency def-weil-pbc-algebra-hom-quotient (Mathlib leaf, no lean record needed):
  `Mathlib.Algebra.Algebra.Hom`, `AlgHom`; `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`; and the standard ideal powers.
- Proof dependency lem-weil-pbc-localization-noetherian (Mathlib leaf):
  `Mathlib.RingTheory.Localization.Submodule`, `IsLocalization.isNoetherianRing`.
- Proof dependency lem-weil-pbc-local-completion-local-ring (Mathlib leaf):
  `Mathlib.RingTheory.AdicCompletion.LocalRing`, its local-ring instance,
  `AdicCompletion.maximalIdeal_eq_map`,
  `AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero`, and
  `AdicCompletion.residueField_map_bijective`.

All recorded statement modules and all recorded proof modules are in the transitive
imports; direct imports provide the completion/localization instances needed to type
this statement. No downstream approximation theorem is imported, avoiding an import cycle.

Edge cases checked before drafting and again on rereading:

- n=0 is allowed (`Fin 0`): generator congruences and generator equalities are vacuous,
  but an R-algebra map from the coefficient quotient is still unique.
- m=0 is allowed: `Ideal.span (Set.range F)` is the zero ideal and evaluation is free.
- Repeated or zero relations are allowed; no linear independence, minimality, smoothness,
  reducedness, domain, finite-type condition on A/A', or nonzero generators are assumed.
- N=1 is allowed and suffices to put J in the completed maximal ideal. N=0 is excluded
  exactly as in the node (otherwise the congruences cannot determine the marked prime).
- Prime ideals rule out the trivial ring only where the mathematics itself does so.
  A zero quotient has no prime q; no unrelated `Nontrivial` hypothesis is added.
- The polynomial congruence includes constants and zero. The fraction clause includes
  zero and units and all representatives, with no denominator selected as extra data.

Searches made on 2026-10-24 using the prescribed msearch.py wrapper:

- LeanFinder: "Congruences on polynomial algebra generators determine the inverse image
  prime and extend to congruences on localized fractions". Eight hits, chiefly
  `Algebra.Generators.compLocalizationAwayAlgHom_X_inl`, localizationAway presentations,
  and `MvPolynomial.isLocalization`; none states this result.
- Loogle: `IsLocalHom, Localization.AtPrime`. Two hits:
  `Localization.isLocalHom_localRingHom` and
  `instIsLocalHomAtPrimeRingHomAlgebraMap`. They supply locality, not generator congruences.
- Mathlib grep: `congruen.*locali|locali.*congruen|localRingHom`, within RingTheory/Localization.
  Hits locate the canonical localRingHom definition and its evaluation rules; no exact match.
- LeanSearch: "Two algebra homomorphisms congruent on polynomial generators induce the
  same prime and congruent maps on the localization". Eight hits include
  `IsLocalization.ringHom_ext`, `MvPolynomial.algHom_ext`, and generated congr_simp lemmas;
  none combines the hypotheses and conclusions of this node.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `lem-trf-generator-congruence-localization|generator.*[Cc]ongruence|congruence.*[Ll]ocaliz`.
  Only a natural-language proof reference in LocalMapCompletionApproximation and unrelated
  log universal-stalk text. No existing declaration of the result.
- Additional project search for `exists_adicCompletion_map_of_local`, completion-map
  definitions, and localRingHom located the upstream coordinate-characterized existence
  theorem and downstream wrappers. The existing existence theorem is used directly.

Validation: scompile.py compiled this module in both sandbox and library namespaces,
with no errors or unexpected warnings (8.8 s and 2.8 s reported). Both auto-implicit
options are disabled. No proofs beyond the single required sorry have been added.
No mathematical statement faults or disputed assertions were found.

## Second reading by Q69

This is an in-thread second pass with the node and module open, not a claim of an
independent agent review; the dispatcher's explicit instruction prohibits starting
other agents, and the maintainer performs the independent delivery review.

Reread the full node against the signature. The separate universes and algebra instances
cover the three commutative rings; both Noetherian hypotheses, both primes and their
inverse-image equality are present. The finite quotient is literal, so there is no
implicit finite-presentation assumption on an arbitrary B. In particular the expression
for each a_i passes through both the quotient and localization before theta. In every
congruence J is the image of the same N-th local maximal-ideal power. The three completed
maps are syntactically the same coordinate-characterized choice. The explicit uniqueness
clause has only generator equalities as its antecedent. The polynomial and fraction
clauses quantify over their whole respective rings, and the prime equality feeds the
canonical localAlgHom used in the final clause. The induced map is asserted local.
Empty variable and relation lists are admitted. No mismatch was found on this second pass;
no statement correction or dependency interface repair was needed.
