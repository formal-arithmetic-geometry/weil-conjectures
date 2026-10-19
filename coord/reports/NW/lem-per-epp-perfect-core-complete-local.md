## Worker report

The module Sheaf.RingTheory.EppPerfectCoreCompleteLocal states
IsLocalRing.epp_perfect_core_complete_local with exactly one postponed proof (`sorry`).
No new definitions, dependency modules, or statement corrections are needed.

Hypotheses and clauses, matched individually to the node:

- Prime p: `(p : ℕ) [Fact p.Prime]`.
- The perfect field k₀ of characteristic p: `(k₀ : Type v) [Field k₀]
  [CharP k₀ p] [PerfectRing k₀ p]`. PerfectRing asserts bijectivity of x ↦ x^p;
  its injectivity is automatic for fields in prime characteristic, so this is
  equivalent to the node's surjectivity convention.
- The commutative local ring: `(R : Type u) [CommRing R] [IsLocalRing R]`.
  Its unique maximal ideal m is `IsLocalRing.maximalIdeal R`, not a separately
  chosen ideal that could differ from the local maximal ideal.
- Noetherian: `[IsNoetherianRing R]`, every ideal finitely generated.
- Integral domain, including 1 ≠ 0: `[IsDomain R]`.
- Characteristic p: `[CharP R p]`.
- The specified inclusion k₀ → R: `[Algebra k₀ R]`. Its `algebraMap` is a
  unital ring homomorphism, necessarily injective from a field into the
  nontrivial domain R. Every inclusion gives precisely this algebra structure.
- Completeness at m: `[IsAdicComplete (maximalIdeal R) R]`. This includes
  separatedness as required; no weaker precompleteness notion is substituted.
- k = R/m: `IsLocalRing.ResidueField R`, definitionally the quotient by m.
- F = Frac(R): `FractionRing R`, the localization at nonzero divisors; these
  are exactly the nonzero elements since R is a domain. Mathlib supplies its field.
- Perfect-core membership in each of these fields E is written directly as
  `∀ n : ℕ, ∃ y : E, y ^ (p ^ n) = x`. This is exactly membership in the
  intersection over n ≥ 0 of the sets of p^n-th powers, without choosing
  a root sequence or requiring extra coherence.
- The antecedent for every element of k's perfect core is `hres`, with
  conclusion `IsAlgebraic k₀ x`.
- The conclusion quantifies over every `x : FractionRing R` satisfying the
  same root condition and asserts `IsAlgebraic k₀ x`.
- Algebraic means precisely a nonzero polynomial vanishing at x: the
  definition of `IsAlgebraic k₀ x` is `∃ P : k₀[X], P ≠ 0 ∧ aeval x P = 0`.
  Both coefficient actions are the induced actions from the specified k₀ → R,
  through the quotient and localization respectively, not arbitrary embeddings.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (mathlib_match).
- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs.
- def-weil-pbc-adically-complete-ring: `IsAdicComplete`,
  Mathlib.RingTheory.AdicCompletion.Basic; its `IsHausdorff` parent retains
  the intersection-of-powers-zero clause.
- Further existing notions: `PerfectRing` (Mathlib.FieldTheory.Perfect),
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`, and its induced algebra
  (Mathlib.RingTheory.LocalRing.ResidueField.Basic/Defs), `FractionRing`
  (Mathlib.RingTheory.Localization.FractionRing), and `IsAlgebraic`
  (Mathlib.RingTheory.Algebraic.Defs). Their signatures and docstrings were read.
- The stated proof input `IsLocalRing.complete_local_domain_finite_over_regular`
  is imported without public from Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular.
  The Mathlib proof leaves `MvPowerSeries` and `LaurentSeries` are imported
  without public from their recorded modules. The remaining proof input
  lem-per-finite-extension-perfect-core has no recorded declaration or
  Mathlib match, so has no module to import; it is not a statement prerequisite.

Source and edge cases:

Read the actual ILO PDF, Exposé IV 3.2.1, 3.2.2, 3.2.3 and 4.2.3
(pdftotext, scratchpad/ilo.txt, lines 2796 onward and 2967 onward).
Its perfect-core definition and coefficient-field Cohen argument agree with the node.
The theorem docstring carries all seven DAG proof steps, including compatibility
with the specified perfect subfield, inseparable finite extensions, and algebraicity
transitivity on finitely many coefficients.

For n = 0 the root condition is `∃ y, y^1 = x`, so it excludes nothing.
Zero is included in both perfect cores and is algebraic via the polynomial T.
A local ring that is already a field (m = 0, dimension zero) is allowed:
its residue and fraction fields are canonically that same field, and no
positive dimension or nonzero maximal ideal is assumed. Imperfect residue fields,
nonseparable finite parameter-field extensions, and arbitrary prime p (including 2)
are allowed. The zero ring is excluded exactly by the node's domain condition.
The independent universes u and v allow every specified field inclusion and
impose no artificial size equality. There are no vacuous test-object quantifiers.
No STATEMENT-DISPUTED issue was found.

Searches for an existing statement (all returned no exact match):

- msearch.py leanfinder: “The perfect core of the fraction field of a complete
  Noetherian local domain is algebraic over a perfect subfield if the perfect
  core of the residue field is algebraic”. Eight results concerned relative
  perfect closure, algebraicity under integral localization, residue fields,
  and formal smoothness; none is this theorem.
- msearch.py loogle: `PerfectRing, IsAlgebraic`: zero hits.
- msearch.py grep: `perfectCore|perfect_core|[Mm]aximal.*perfect|[Pp]erfect.*[Ss]ubfield`:
  three unrelated hits (perfect pairings, relative purely inseparable closure,
  ideal norms); no maximal-perfect-subfield transfer theorem.
- msearch.py leansearch: “For a complete Noetherian local domain in characteristic p
  over a perfect field, algebraicity of the perfect core of its residue field
  implies algebraicity of the perfect core of its fraction field”. Eight hits:
  IsFractionRing.isAlgebraic_iff, integral-residue algebraicity, PerfectClosure,
  relative perfectClosure and perfection of algebraic extensions; no match.
- rg in /home/ubuntu/weil-src-slopmaster2/WeilConjectures and lean/Sheaf:
  `perfectCore|perfect_core|PerfectCore|epp.*perfect|Epp.*perfect` and the exact
  node id. No matching theorem; only perfect-complex cores and the consumer's
  docstring referring to this unstated lemma. A second search using
  `perfect.*[Cc]ore|[Mm]aximal.*perfect|[Pp]erfect.*[Ss]ubfield|epp_perfect_core`
  included dag/lean_names_upstream.json and found no matching declaration.

## Second reading by NW

A separate clause-by-clause rereading of the node and completed file checked the
prime and characteristic binders, perfectness, local/Noetherian/domain/completeness
conditions, the specified inclusion, induced coefficient actions, and both perfect-core
quantifiers against the signature. No mismatch or node change was found. The use
of PerfectRing adds no restriction because Frobenius on a field is injective.
The canonical residue and fraction fields preserve the exact objects in the node.
No extra separability, coefficient-field choice, root coherence, positive dimension,
or assumption that the residue field itself is algebraic has been introduced.
This is a rereading by the same worker: the dispatcher explicitly forbids starting
another agent; the maintainer supplies the independent delivery review.

## Validation

scompile.py compiled this module in both sandbox and library contexts with exit
code 0 and no diagnostics (2.3 s and 2.2 s, respectively). The only proof is
`by sorry`. The prescribed deliver2.py dry run and push supply the final preflight
and repeat per-file compilation.
