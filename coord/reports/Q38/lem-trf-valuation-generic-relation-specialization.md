## Worker report

The module `Sheaf.RingTheory.ValuationGenericRelationSpecialization` states
`ValuationRing.exists_relation_coeff_one_and_residue_relation`, with `sorry` as
its sole proof. It introduces no definitions and changes only the item's `lean`
record. The mathematical source read was Stacks Project, `algebra.tex`, Tag 00QK,
label `lemma-finite-type-domain-over-valuation-ring-dim-fibres`, including the
whole statement and proof. Its coefficient-normalization argument needs neither
finite type nor quasi-finiteness, as the accepted split spells out.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The valuation domain A is `(A : Type u) [CommRing A] [IsDomain A]
  [ValuationRing A]`. Mathlib's divisibility-comparability definition is equivalent
  to the fraction-field membership criterion in the node. No discreteness,
  rank, characteristic, or nonfield condition is imposed. The class provides
  `IsLocalRing A`, so the maximal ideal is canonical.
- The field of fractions K is `(K : Type w) [Field K] [Algebra A K]
  [IsFractionRing A K]`. This permits every realization of Frac(A), and does not
  restrict its universe to that of A or B.
- The residue field k = A/m_A is `IsLocalRing.ResidueField A`; the quotient map is
  `IsLocalRing.residue A`. These are Mathlib's quotient and canonical map.
- B is `(B : Type v) [CommRing B] [IsDomain B] [Algebra A B]`. Containment of A
  is `hAB : Function.Injective (algebraMap A B)`, rather than an arbitrary
  possibly noninjective algebra structure.
- The integer n >= 0 is `n : ℕ`; the variables are `Fin n`.
- The map alpha is `α : MvPolynomial (Fin n) A →ₐ[A] B`. It is not required to
  be surjective, finite type, quasi-finite, or injective.
- H is precisely `B ⊗[A] K`, with Mathlib's tensor algebra ring multiplication.
  The unconditional conclusion `IsDomain (B ⊗[A] K)` includes nonzeroness.
  This is a conclusion, not an extra hypothesis assumed to type the theorem.
- L is precisely `FractionRing (B ⊗[A] K)`. Its K-algebra structure, passed
  explicitly to `Algebra.trdeg`, is the algebra of the ring homomorphism
  `K → B ⊗[A] K → FractionRing (B ⊗[A] K)`, where the first map is
  `Algebra.TensorProduct.includeRight.toRingHom` and the second is the
  fraction-ring map. This writes the canonical action without a local instance
  or an independently supplied algebra structure. `FractionRing` is defined
  for commutative rings and `Algebra.trdeg` for commutative algebras, so neither
  expression needs to assume the domain conclusion in advance. The domain
  conclusion ensures this fraction ring is mathematically a field.
- The hypothesis is exactly this `Algebra.trdeg K L < (n : Cardinal)`, in the
  implication forming the second conjunct. The domain assertion precedes it
  and is unconditional, as in the node.
- The witness is `∃ h : MvPolynomial (Fin n) A`; its kernel condition is
  `α h = 0` and its normalized coefficient is
  `∃ I : Fin n →₀ ℕ, MvPolynomial.coeff I h = 1`.
- The coefficientwise reduction is
  `MvPolynomial.map (IsLocalRing.residue A) h`, and its nonzeroness is the
  explicit third conjunct after the existential witness.
- The induced alpha_k is written directly with `MvPolynomial.eval₂Hom`:
  coefficients use `Algebra.TensorProduct.includeRight` from k into B tensor k;
  variable i is sent to `α (MvPolynomial.X i) ⊗ₜ[A] (1 : IsLocalRing.ResidueField A)`.
  This is the canonical scalar extension of alpha, by the polynomial universal
  property, without a new helper definition or an arbitrary supplied map.
  Its value on the reduction is explicitly `= 0`, i.e. membership in its kernel.
- No further hypothesis on B, alpha, H's size, or the residue tensor is present.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and
  `MvPolynomial.algHom_ext` in `Mathlib.Algebra.MvPolynomial.Basic`, and
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`. The latter module
  is publicly imported; the concrete maps also use its `MvPolynomial.map` and
  `MvPolynomial.eval₂Hom`.
- `def-weil-pbc-module-tensor-product`: the Mathlib leaf `TensorProduct` and
  `TensorProduct.tmul` in `Mathlib.LinearAlgebra.TensorProduct.Defs`. The public
  import `Mathlib.RingTheory.TensorProduct.Basic` supplies this same product
  together with its usual algebra multiplication and `includeRight`.
- `def-kun-transcendence-degree`: `Algebra.trdeg` in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, publicly imported.
- The proof-only dependency
  `lem-weil-pbc-generic-fibre-localization-domain-irreducible` is a Mathlib leaf,
  recorded via `IsLocalization.tensor` and
  `IsLocalization.isDomain_of_le_nonZeroDivisors`; its recorded module
  `Mathlib.RingTheory.Localization.BaseChange` is imported without `public`.
  No new proof dependency or replacement interface is needed.
- Additional standard notions use `ValuationRing` and its `isLocalRing`
  instance (`Mathlib.RingTheory.Valuation.ValuationRing`),
  `IsLocalRing.ResidueField` and `IsLocalRing.residue`
  (`Mathlib.RingTheory.LocalRing.ResidueField.Defs`, via `Basic`), and
  `FractionRing`/`IsFractionRing`
  (`Mathlib.RingTheory.Localization.FractionRing`).

Edge cases checked before writing:

- n = 0 is included. The strict transcendence-degree inequality is impossible;
  the unconditional domain assertion still applies.
- A may itself be a field: its maximal ideal is zero and reduction is the
  identity up to the canonical quotient identification.
- Arbitrary-rank valuation rings are included. Finite comparability of ratios,
  rather than a discrete valuation or a global minimal-valuation hypothesis,
  supplies the coefficient normalization in the proof docstring.
- B tensor k may be zero. For A = Z_(p), B = Frac(A), n = 1 and alpha(t) = 1/p,
  h = 1 - p*t has a coefficient 1, evaluates to zero, and reduces to 1 while
  alpha_k has zero target. The statement has no `Nontrivial` instance on that
  target, so it preserves this example.
- For A = Z_(p), B = A[x, x^2/p], the relation t_1^2 - p*t_2 has coefficient 1
  and a nonzero reduction. Neither finite generation nor any rank condition
  is used by the formulation.
- With B = A[t] and n = 1 for its tautological variable, trdeg is 1; the strict
  inequality excludes a nonexistent relation.
- The independent explicit universes u, v, w allow larger containing domains
  and any realization of the fraction field. There is no quantified test-object
  universe that could make a hypothesis vacuous.

Searches for an existing statement (all made with the prescribed wrapper):

- LeanFinder: "An algebraic dependence over the fraction field of a valuation
  ring specializes to a polynomial relation with a coefficient equal to one
  over the valuation ring and nonzero residue reduction". Eight hits, including
  Proj's valuative criterion, integral Weierstrass curves, and valuation/minpoly
  or denominator-clearing lemmas; none states this multivariate normalization
  with kernel descent and nonzero residue reduction.
- Loogle: `ValuationRing, MvPolynomial`: zero hits.
- Mathlib grep: `[Vv]aluation.*[Pp]olynomial|[Pp]olynomial.*[Vv]aluation|exists.*coeff.*one`
  in `RingTheory`: 22 hits concerning power-series evaluation, Laurent-series
  valuation, and minpoly coefficients; no matching statement.
- Direct `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `valuation.*(relation|specializ)|generic.*relation|relation.*specializ|exists.*coeff.*one`
  found unrelated evaluation and normalized rational-factor declarations.
  Direct `grep -rn` for the item ID in `lean/WeilConjectures` found no match.
  `dag/lean_names_upstream.json` also has no corresponding item or relation name.
  These searches do not reveal a duplicate of the delivered theorem.

No statement correction, new node, dependency-module repair, or
STATEMENT-DISPUTED flag is needed. The declaration docstring records all five
steps of the accepted natural-language proof and the nodes those steps use.

## Second reading by Q38

This section was written by the maintainer's independent second reader (cc review
service, 2026-10-24); the worker's earlier self-check under this heading was the
worker's own rereading and is replaced by this reading. The Lean file, the node and
all other records of delivery 4e7da2d9 are unchanged.

Node statement as a list, with the Lean rendering and verdict:

1. Valuation ring `A` (domain, `x ∈ A` or `x⁻¹ ∈ A` for `x ∈ K^×`):
   `(A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]`. Mathlib's
   divisibility-comparability class is equivalent for domains. No rank,
   discreteness or nonfield condition. Correct.
2. `K = Frac(A)`: `(K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]`,
   any realization, independent universe. Correct.
3. `k = A/𝔪_A`: `IsLocalRing.ResidueField A` with `IsLocalRing.residue A`
   (local structure from the `ValuationRing` instance). Correct.
4. `B` a domain containing `A`: `(B : Type v) [CommRing B] [IsDomain B] [Algebra A B]`
   with `hAB : Function.Injective (algebraMap A B)`. Correct, no finite type.
5. `n ≥ 0`, `α : A[t_1..t_n] → B` an `A`-algebra map [def-weil-pbc-mv-polynomial-ring]:
   `(n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B)`. Correct, no further condition.
6. `H = B ⊗_A K` [def-weil-pbc-module-tensor-product] with tensor algebra
   multiplication: `B ⊗[A] K` (Mathlib `TensorProduct`, algebra structure of
   `Mathlib.RingTheory.TensorProduct.Basic`). Correct; factor order as in the node.
7. "H is a nonzero domain": the unconditional conjunct `IsDomain (B ⊗[A] K)`
   (includes `Nontrivial`). It is a conclusion, as in the node, and it is true
   (H is the localization of B at the image of `A ∖ {0}`, which avoids 0 by `hAB`).
8. `L = Frac(H)`, `trdeg_K L < n` [def-kun-transcendence-degree]: `FractionRing (B ⊗[A] K)`
   with `K`-algebra structure the composite `K → B ⊗[A] K → FractionRing`
   (`includeRight` then `algebraMap`), passed explicitly to `@Algebra.trdeg`;
   `< (n : Cardinal)`. This is the canonical structure (the `K`-structure on
   `B ⊗[A] K` is not an instance, so explicit passing is needed, and no other choice
   is made). Correct.
9. `h ∈ A[t]` with `α(h) = 0` and some coefficient `1`: `∃ h, α h = 0 ∧
   ∃ I, coeff I h = 1`. Correct.
10. `h̄` nonzero: `MvPolynomial.map (IsLocalRing.residue A) h ≠ 0` — coefficientwise
    reduction. Correct.
11. `h̄ ∈ ker α_k`, `α_k : k[t] → B ⊗_A k`: `eval₂Hom includeRight
    (fun i ↦ α (X i) ⊗ₜ 1) h̄ = 0`. This is the scalar extension `α ⊗ k`
    (coefficients `c ↦ 1 ⊗ c`, variables `t_i ↦ α(t_i) ⊗ 1`), fixed by the
    polynomial universal property; not an arbitrary map. Correct.
12. Quantifier order: the domain claim is unconditional, the trdeg hypothesis governs
    only the existence of `h`, as in the node.

Source place read: Stacks `algebra.tex`, Lemma 00QK
(`lemma-finite-type-domain-over-valuation-ring-dim-fibres`) and its proof: the nonzero
kernel of `K[t] → S ⊗_R K`, division by a coefficient of minimal valuation, reduction to
`k[t] → S ⊗_R k`. The node isolates exactly this paragraph; finite type and
quasi-finiteness are used in the source only around it, so their absence here is right.
Parent `lem-trf-valuation-domain-fibre-dimensions` step 3 uses exactly these
conclusions.

Edge cases: `n = 0` (trdeg ≥ 0, hypothesis impossible; domain claim still stated);
`A` a field (`𝔪 = 0`); arbitrary rank valuation (finite comparability of ratios
suffices); `B ⊗_A k = 0` (no `Nontrivial` on the target; e.g. `B = Frac A`,
`α(t) = 1/p`, `h = 1 - p t`); `B = A[t]`, `n = 1` (trdeg 1, hypothesis false).
Universes `u, v, w` independent; no quantified test object.

One definition per notion: no new definitions; dependency leaves are Mathlib
`MvPolynomial`, `TensorProduct`, `Algebra.trdeg`, as recorded. `rg` over
`lean/Sheaf` for `Algebra.trdeg`, `coeff … = 1`, `residue A) h` found no duplicate of
this statement; `ValuationDomainFibreDimensions` and
`ValuationFibreInjectiveSourcePresentation` state other results.

Conventions: proof is `by sorry` only; module and theorem docstrings carry the source
place and `(blueprint: lem-trf-valuation-generic-relation-specialization)`; the theorem
docstring carries the five proof steps of the node; `autoImplicit` off, all variables
and universes bound; `lean.statement` is the verbatim signature. Only the item's `lean`
record changed. No mismatch found.
