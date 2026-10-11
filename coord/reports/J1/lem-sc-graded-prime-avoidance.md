## Worker report

The module `lean/Sheaf/RingTheory/GradedPrimeAvoidance.lean` states
`HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime`, with its sole proof `sorry`.
The node copy changes only `lean`. There are no new nodes, dependency modules, statement
corrections, or disputed statements.

Source checked: Stacks Project, Algebra Lemma 10.57.6, Tag 00JS,
https://stacks.math.columbia.edu/tag/00JS (`algebra-lemma-graded-silly`). The local
`literature/stacks-project/algebra.tex` is absent on this machine, so the authoritative
Stacks page was read directly. Its statement agrees with the node. The declaration docstring
contains the complete five-step node proof: discard included primes, the single-prime
homogeneous-component argument, induction, product-ideal noncontainment, and the sum of
powers of equal positive degree. It also explicitly covers the empty-family case.

Hypothesis and conclusion correspondence:

- The commutative ring `S` is `{A : Type u} [CommRing A]`. There is no nontriviality,
  Noetherian, field, or characteristic assumption.
- The nonnegative grading `S = ⨁ n ≥ 0, S_n` is `(𝒜 : ℕ → σ) [GradedRing 𝒜]` with
  `{σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]`. GradedRing supplies the internal
  direct-sum decomposition and multiplication of components in summed degree. The generic
  component type is exactly the representation accepted by Mathlib's Proj construction;
  it includes `AddSubgroup A` for every nonnegatively graded commutative ring.
- The finite list of homogeneous primes is `(r : ℕ) (p : Fin r → HomogeneousIdeal 𝒜)`.
  `Fin r` merely numbers the original finite list, allowing empty lists and repeated primes.
  HomogeneousIdeal includes precisely closure under homogeneous components.
- Primality is `(hp : ∀ i : Fin r, (p i).toIdeal.IsPrime)`, including properness of each prime.
- The graded ideal is `(I : HomogeneousIdeal 𝒜)`.
- `I ⊆ S_+` is `(hI : I ≤ HomogeneousIdeal.irrelevant 𝒜)`; the irrelevant ideal is the
  kernel of the degree-zero projection, equivalently the sum of positive components.
- Not contained in any prime is `(hIp : ∀ i : Fin r, ¬ I ≤ p i)`.
- Positive degree is `∃ (n : ℕ), 0 < n`.
- A homogeneous element of that degree is `∃ (x : A), x ∈ 𝒜 n`.
- Membership in the given ideal is `x ∈ I`.
- Avoiding every listed prime is `∀ i : Fin r, x ∉ p i`.

Dependency declarations read and used:

`def-pc-proj` is a Mathlib leaf with no lean record, and its mathlib_match names
`AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec` in
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, and `ProjectiveSpectrum.basicOpen`
in `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology`. Their complete signatures,
ambient binders and docstrings were read. This lemma does not construct Proj, a standard
open, or a scheme isomorphism: the dependency supplies the nonnegative grading and `S_+`
notation. The module uses exactly the existing Mathlib definitions underlying those recorded
declarations, rather than adding a definition of them. Importing Scheme or applying Proj
would be unused here. The existing dependency record needs no repair.

The two used imports are `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal` (giving
`GradedRing`, `HomogeneousIdeal`, `HomogeneousIdeal.toIdeal`, and
`HomogeneousIdeal.irrelevant`) and `Mathlib.RingTheory.Ideal.Prime` (giving `Ideal.IsPrime`).
The relevant signatures and docstrings were read in the pinned Mathlib source, including
`Ideal.IsHomogeneous`, `HomogeneousSubmodule`, the direct-sum `Decomposition`,
`irrelevant_eq_iSup` and `mem_irrelevant_iff`. No private notion is introduced.

Edge cases checked before writing:

- `r = 0`: choose `n = 1` and `x = 0`. Zero lies in every component and every ideal;
  avoidance is vacuous. No nonzero condition is stated in the source or Lean.
- Zero ring: the empty case still holds, and a nonempty prime family is impossible.
- `I = ⊥` or `S_+ = ⊥`: for a nonempty family the noncontainment hypothesis is impossible;
  for an empty family the same zero witness works, even if all positive components are zero.
- `r = 1`: homogeneity extracts a component outside the prime; containment in the
  irrelevant ideal makes the zeroth component zero, so the witness has positive degree.
- Repeated or nested primes are allowed and handled by the source's initial reduction.
- `n = 0` is excluded only in the conclusion, exactly as the positive-degree source requires.
  All ring characteristics and arbitrary ring/component universes are retained.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "homogeneous element of a graded ideal outside finitely many
  homogeneous prime ideals"`: eight hits, concerning relevance, irrelevant ideals, or
  homogeneous primality; none states avoidance for an arbitrary graded ideal.
- `msearch.py ... loogle "HomogeneousIdeal, Ideal.IsPrime"`: two hits,
  `ProjectiveSpectrum.mk` and `HomogeneousIdeal.isPrime_comap`; neither is this theorem.
- `msearch.py ... grep "avoid|IsHomogeneous|irrelevant" RingTheory/GradedAlgebra`:
  23 hits defining homogeneous notions or radical properties; no graded prime avoidance.
- `msearch.py ... leansearch "graded prime avoidance homogeneous ideal positive degree
  finitely many prime ideals"`: service unavailable (Internal Server Error), recorded
  without claiming a no-match result.
- Local `rg` of `graded.*prime|prime.*avoid|exists_homogeneous_notMem` in Mathlib,
  `WeilConjectures` and `lean/Sheaf`: the source theorem
  `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset` is only the special case
  `I = S_+`. Its full signature, docstring and proof were read in
  `WeilConjectures/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean:54`.
  Mathlib's `Ideal.subset_union_prime` is ungraded and does not supply homogeneity.
- Local `rg` for the node id in `WeilConjectures`: no hits.
- Local `rg` for the chosen name `exists_homogeneous_mem_notMem_of_isPrime` in
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: `scompile.py J1 lem-sc-graded-prime-avoidance` on this module returned exit
code zero, compiled in 1.2 seconds, without warnings. Every variable and universe is explicitly
bound. The node's `lean.statement` is the verbatim multiline signature preceding `:=`.


## Second reading by J1

Independent second reading of the node, Lean module, dependency node and source on
2026-10-11. No mathematical or Lean mismatch was found; no Lean or node content changed.
The second reading adds this report only.

Source: [Stacks Tag 00JS](https://stacks.math.columbia.edu/tag/00JS), Algebra
Lemma 10.57.6, and the raw Stacks `algebra.tex`, downloaded into the item's scratchpad.
I read `lemma-graded-silly` and the opening of `section-proj`: homogeneous ideals
contain each component of every member; the section imposes no Noetherian, field,
finite-generation or characteristic hypothesis. The nonnegative grading is the
one in the node and in this section's explicit direct-sum notation.

Objects, hypotheses and conclusion, listed independently and matched in order:

- A commutative ring S: `{A : Type u} [CommRing A]`. Exact; no nontriviality required.
- Its direct-sum nonnegative grading, additive subgroup components and multiplication
  in summed degree: `{σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]`,
  `(𝒜 : ℕ → σ) [GradedRing 𝒜]`. Exact: I read `GradedRing` in GradedAlgebra.Basic
  and `DirectSum.Decomposition`, which supplies mutually inverse decomposition and
  canonical summation. Taking σ to be `AddSubgroup A` covers every grading of the node;
  this representation introduces no extra algebraic condition.
- A finite list of homogeneous prime ideals p₁,...,pᵣ: `(r : ℕ)` and
  `(p : Fin r → HomogeneousIdeal 𝒜)`. Exact; no distinctness or noncontainment assumed.
- Primality of every listed ideal: `(hp : ∀ i : Fin r, (p i).toIdeal.IsPrime)`.
  Exact; I read `Ideal.IsPrime`, including properness and the product condition.
- A graded ideal I: `(I : HomogeneousIdeal 𝒜)`. Exact; I read the abbreviation
  `HomogeneousIdeal`, `toIdeal`, `Ideal.IsHomogeneous`, and its component-membership
  characterization. Membership and order are the underlying ideal's membership and order.
- Containment I ⊆ S₊: `(hI : I ≤ HomogeneousIdeal.irrelevant 𝒜)`. Exact;
  `irrelevant` is the kernel of the zero-component projection and `irrelevant_eq_iSup`
  identifies its additive submonoid with the sum of all positive components.
- I is not contained in any listed prime: `(hIp : ∀ i : Fin r, ¬ I ≤ p i)`.
  Exact; there is no extra relevance assumption on the primes.
- A positive degree for the witness: `∃ (n : ℕ), 0 < n`. Exact.
- One homogeneous element x of this degree: `∃ (x : A), x ∈ 𝒜 n`. Exact;
  the degree and element existential quantifiers commute and precede universal avoidance.
- The same x belongs to I: `x ∈ I`. Exact.
- The same x avoids every prime: `∀ i : Fin r, x ∉ p i`. Exact; the witness is
  simultaneous, not a separately chosen element for each prime.

Dependency reading (H3/H4/H13): I opened `def-pc-proj` and the signatures and ambient
binders of `AlgebraicGeometry.Proj`, `AlgebraicGeometry.projIsoSpec` and
`ProjectiveSpectrum.basicOpen` in its Mathlib match. They use the same ℕ-indexed
`GradedRing`, `HomogeneousIdeal` and irrelevant ideal. Here only that underlying graded
ring vocabulary is needed; the node's scheme, localization and standard-open construction
are not conclusions of this lemma. There is no unusable prerequisite and no private copy.
The two imports supply the used homogeneous ideal and primality declarations. There are
no new definition nodes, dependency modules or statement corrections to review.

Edge cases: r = 0 permits x = 0 in degree 1; homogeneity means component membership,
not nonzeroness, so even a grading with zero positive components is covered. In the zero
ring a nonempty prime list is impossible, while the empty case works. For I = 0 or
S₊ = 0, a nonempty list contradicts hIp; the empty case remains covered. A single prime,
repeated primes and nested primes are allowed. Degree zero is excluded only for the
conclusion's degree, as required. All characteristics and arbitrary independent universes
u and v are retained. Empty schemes are not additional objects of this ring lemma.

Independent searches using different wording:

- LeanFinder via `msearch.py`: "graded ideal contains an element in one homogeneous
  component avoiding a finite union of primes". Eight hits: homogeneous primality
  criteria, relevance and irrelevant-ideal membership/containment characterizations;
  no arbitrary-ideal finite homogeneous avoidance statement.
- Loogle via `msearch.py`: `HomogeneousIdeal, ∃ _, _ ∉ _`. Zero hits.
- LeanSearch via `msearch.py`: "a homogeneous element in an ideal outside a finite union
  of homogeneous prime ideals". Service returned Internal Server Error; unavailable,
  not counted as evidence of absence.
- Local rg: `avoidance|subset_union_prime|exists.*notMem|exists.*not_mem` in Mathlib's
  graded algebra and ideal sources, upstream ProjectiveSpectrum and repository
  lean/Sheaf; also `homogeneous.*(avoid|outside)|prime.*avoid` across upstream and
  lean/Sheaf, and the declaration name/node id in the upstream-name map and sources.
  No exact declaration. I opened the full upstream
  `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset` declaration and proof: its
  inputs are finitely many relevant Proj points and it asks no membership in arbitrary
  I; it covers only I = S₊. I also opened `Ideal.subset_union_prime` in Mathlib: it is
  ungraded, so it does not state the requested homogeneous witness conclusion.

H5/H6/H8/H9: one named theorem, its proof only `sorry`, no definitions or hollow data.
The declaration and module docstrings name 00JS and the blueprint id. The declaration
proof text covers all five node steps (removing inclusions, the one-prime component,
induction, product noncontainment, equal-degree powers and sum), plus the empty list.
Every variable and both universes are explicitly bound, and lines satisfy the width rule.
The node's lean.statement was checked verbatim against the multiline theorem signature;
all other node fields are unchanged. Clean server compilation and delivery preflight are
required below; the second reader reran them before pushing.
