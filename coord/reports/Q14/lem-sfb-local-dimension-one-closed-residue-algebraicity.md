## Worker report

States `Ideal.trdeg_residueField_eq_zero_of_local_dim_le_one` in
`Sheaf.RingTheory.LocalDimensionOneClosedResidueAlgebraicity`. The single theorem
has proof `by sorry`; there are no definitions or additional postponed facts.
The source is Stacks Project, Varieties, Tag 0AB6,
`lemma-quasi-finite-in-codim-1`, proof of condition (2), read at
`literature/stacks-project/varieties.tex:3188–3265`. The declaration docstring
carries all four proof steps of this DAG node, including the vertical component.
No statement correction, missing notion, dependency repair, or disputed statement.
Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings B and C: `{B : Type u} {C : Type v} [CommRing B] [CommRing C]`.
  Explicit independent universes impose no equality of their sizes.
- B is Noetherian and local: `[IsNoetherianRing B] [IsLocalRing B]`.
  `IsLocalRing.maximalIdeal B` is its unique maximal ideal m. Local rings here
  are nontrivial, exactly as the existence of a maximal ideal requires.
- Dimension at most one: `hdim : ringKrullDim B ≤ 1`, in `WithBot ℕ∞`.
- C is a finite type B-algebra: `[Algebra B C] [Algebra.FiniteType B C]`.
  The recorded dependency's `RingHom.FiniteType` is the same notion for
  `algebraMap B C`, by `RingHom.finiteType_algebraMap`; its mathlib_match also
  explicitly records `Algebra.FiniteType`. No finite-module assumption is used.
- Every minimal prime Q of C: `∀ (Q : Ideal C) [Q.IsPrime],
  Q ∈ minimalPrimes C → ...`. Prime evidence is needed to form κ(Q), and is
  already implied by membership in `minimalPrimes C`; the binder adds no
  mathematical assumption. This is minimal over zero, with no reducedness.
- Its contraction q is `Q.comap (algebraMap B C)`; comap of a prime is prime.
- The canonical field extension κ(q) → κ(Q) is
  `Ideal.ResidueField.map (Q.comap (algebraMap B C)) Q (algebraMap B C) rfl`.
  Its `.toAlgebra` is supplied explicitly to `@Algebra.IsAlgebraic`.
  This means every element has a nonzero annihilating polynomial, exactly the
  definition read in `Mathlib.RingTheory.Algebraic.Defs`.
- Arbitrary prime P over m: `(P : Ideal C) [P.IsPrime]` and
  `hP : IsLocalRing.maximalIdeal B = P.comap (algebraMap B C)`.
  The equality has merely been oriented to match the canonical residue-map API.
- Conclusion: `@Algebra.trdeg (IsLocalRing.maximalIdeal B).ResidueField
  P.ResidueField _ _ (Ideal.ResidueField.map ... hP).toAlgebra = 0`.
  `Ideal.ResidueField` has the canonical `IsFractionRing (B ⧸ m)` instance.
  For maximal m, `Ideal.bijective_algebraMap_quotient_residueField` says that
  `B ⧸ m → κ(m)` is bijective; the map's compatibility on B is
  `Ideal.ResidueField.map_algebraMap`. Thus this conclusion is precisely
  trdeg over B/m with its induced coefficient action, expressed using its
  canonical fraction-field model. It does not quantify an arbitrary action.
- The assertions allowing nonreduced rings, dimension zero, vertical components,
  and empty closed fibre impose no extra restrictions: none are excluded by
  any binder. The theorem is universally quantified in P.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg` (all ideals finitely generated).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (prime-chain supremum).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`,
  `Algebra.FiniteType`, `RingHom.finiteType_algebraMap`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`, its fraction-field instance and maximal-quotient
  bijection. These implement the residue-field clause of the recorded
  localization dependency, whose record lists `Ideal.ResidueField`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`: `minimalPrimes` and the proof
  dependency `Ideal.exists_minimalPrimes_le`. This is a public import because
  minimal primes also occur in the signature.
- `Sheaf.RingTheory.AffineDimensionInequality`:
  `Ideal.height_add_trdeg_residueField_le`, read with its full signature and
  proof docstring; imported privately for the planned proof.

Edge-case checks before writing:

- Nonreduced B and C are permitted: no `IsDomain` or `IsReduced` instance.
  Quotients by the selected primes are used only in the proof plan.
- If dim B = 0, every prime contraction is the maximal ideal; the vertical
  argument proves the conclusion. For example, B = k[ε]/(ε²), C = B has
  algebraic residue extensions and fits all the hypotheses.
- A vertical component contracting to m is explicitly included in `hgeneric`;
  for a one-dimensional local base and C = B/m, its only minimal prime is such
  a component and its residue degree is zero.
- A horizontal localization with empty closed fibre, e.g. a DVR with its
  uniformizer inverted, has algebraic generic extension; no P satisfies hP.
- C may be the zero ring: it has no prime P, so the assertion is vacuous.
  B cannot be the zero ring because a local ring with a maximal ideal is
  nontrivial; this is already part of the node's hypothesis, not a restriction.
- No characteristic, equidimensionality, finite-module, injectivity of B → C,
  separability, or nonempty-fibre assumption has been added.

Searches performed using the prescribed msearch.py wrapper (2026-10-24):

- LeanFinder: "Finite type algebra over Noetherian local ring of dimension at
  most one with algebraic residue fields at minimal primes has algebraic closed
  fibre residue fields". Eight hits: quasi-finite residue fields, integral
  residue extensions, quotient residue algebraicity, and essential finite type
  residue maps. All require different hypotheses or give preliminary facts;
  none states the present theorem.
- LeanSearch: "A finite type algebra over a Noetherian local ring of dimension
  at most one whose minimal prime residue fields are algebraic has closed
  residue transcendence degree zero". Eight hits, including `trdeg_eq_zero`,
  `trdeg_eq_zero_iff`, `trdeg_lt_aleph0`, and integral/quasi-finite residue-field
  results. No local-dimension argument or exact theorem.
- Loogle: `"trdeg", "height"`: zero hits.
- Mathlib grep: `trdeg.*height|height.*trdeg|algebraic.*ringKrullDim|ringKrullDim.*algebraic`:
  zero hits.
- Project rg, in both `lean/WeilConjectures` and `lean/Sheaf`: searched
  `local.*dimension.*one.*residue|trdeg.*minimalPrimes|algebraic.*minimalPrimes|closedResidue.*local`.
  The only broad-pattern hit was `RelativeNodalPointPinching.lean`, about a
  different construction. More targeted minimalPrimes/IsAlgebraic and local
  dimension searches found no matching theorem. The grep for the item's exact
  blueprint id in WeilConjectures found no declaration. Candidate full name and
  module were absent from Mathlib, both project roots and the upstream-name index.

Validation: scompile.py compiled the delivered file in sandbox form and in
library-module form, both clean (1.1 s and 1.0 s). All universes and variables
are explicitly bound and `autoImplicit` is false. Dry-run validation and final
push are recorded by the prescribed delivery wrapper.

## Second reading by Q14

Worker consistency pass only; no second agent was started, as the dispatcher's
brief prohibits it. Independent mathematical review is the maintainer's review
of this delivery. On rereading the node and the final file, checked every clause
above, the order of implicit ring/algebra arguments, and the canonical action in
both `hgeneric` and the conclusion. In particular, the maximal residue-field
model is canonically B/m, the prime-instance binder adds no extra restriction to
minimal primes, and arbitrary nonreduced algebras and empty fibres remain
allowed. No mismatch or change was found in this consistency pass.
