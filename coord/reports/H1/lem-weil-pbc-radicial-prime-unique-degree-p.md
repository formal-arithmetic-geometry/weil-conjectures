## Worker report

The module `Sheaf.RingTheory.RadicialPrimeUniqueDegreeP` states
`AdjoinRoot.radicial_prime_unique_degree_p`. Its only proof is `sorry`.
The node's statement is unchanged; there are no new nodes or dependency modules.

Hypothesis and clause correspondence:

- A prime number p: `(p : ℕ) (hp : p.Prime)`.
- A commutative integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
- p = 0 in R: `(hchar : (p : R) = 0)`. This directly renders the given vanishing,
  without asking for a separately supplied characteristic instance.
- f in R: `(f : R)`.
- C = R[z]/(z^p-f): every occurrence of `AdjoinRoot (X ^ p - C f)`.
  Mathlib's `AdjoinRoot` is definitionally `Polynomial R ⧸ Ideal.span {X ^ p - C f}`;
  `Polynomial.C f` is the constant polynomial, not the informal quotient-ring name C.
- C is an integral domain: `[IsDomain (AdjoinRoot (X ^ p - C f))]`.
- Clause (1), injective structure map: `Function.Injective (of (X ^ p - C f))`.
  Mathlib's `AdjoinRoot.of` is the quotient map composed with `Polynomial.C`.
- Clause (1), integral over R: `∀ c : AdjoinRoot (X ^ p - C f), IsIntegral R c`.
  This says each quotient element satisfies a monic polynomial over the canonical
  R-algebra structure. This is exactly integrality, rather than an additional finiteness claim.
- Clause (2): `∀ c : AdjoinRoot (X ^ p - C f), c ^ p ∈ (of (X ^ p - C f)).range`.
- Clause (3), every base prime: `∀ P : Ideal R, P.IsPrime → ...`.
- Clause (3), exactly one prime above it: `∃! Q : Ideal (AdjoinRoot (X ^ p - C f)),
  Q.IsPrime ∧ Q.comap (of (X ^ p - C f)) = P`. Uniqueness is of the ideal Q among
  prime ideals with the specified contraction; it does not assert uniqueness of all ideals.

Dependency declarations read in the pinned source:

- `def-weil-polynomial-ring`: `Polynomial`, module `Mathlib.Algebra.Polynomial.Basic`,
  structure wrapping `AddMonoidAlgebra R ℕ`; imported transitively by AdjoinRoot.
- `def-weil-pbc-integral-closure`: `integralClosure` and `IsIntegral`, module
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (explicit import). Read the
  `integralClosure` carrier and `IsIntegral` definition in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: a root of a monic polynomial.
  Also read the recorded `IsIntegrallyClosedIn` signature/docstring in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`; this unused clause of the
  dependency is not an extra hypothesis of our statement.
- Supporting existing notions: `AdjoinRoot`, `AdjoinRoot.of`, its canonical `Algebra`
  instance, all in `Mathlib.RingTheory.AdjoinRoot`; `Ideal.IsPrime` and `Ideal.comap`.
  No private copy of any notion is introduced.

Edge cases checked before writing: p = 0 and p = 1 are excluded by primality;
characteristic zero is excluded by p = 0 in the nontrivial domain R. Zero rings are
excluded by the stated domain hypotheses. For f = 0 the quotient has a nonzero
nilpotent root when p is prime, so the quotient-domain hypothesis correctly excludes
that case. For R a field and a valid domain quotient, the sole base prime (0) has the
sole quotient prime (0). The theorem does not impose perfectness, algebraic closure,
Noetherianity, or that f have a root in R. No universe restriction beyond the quotient
being constructed from R: `R : Type u`, with u explicitly declared. No `let` binders,
auto-bound implicits, or independent test-object universes.

Source checked: the local `literature/stacks-project/*.tex` files are absent on this
machine, so opened the official Stacks pages
[07PR](https://stacks.math.columbia.edu/tag/07PR),
[0BR8](https://stacks.math.columbia.edu/tag/0BR8), and
[00GQ](https://stacks.math.columbia.edu/tag/00GQ).
The degree-p quotient construction is in 07PR's proof; 0BR8 gives uniqueness via powers
and 00GQ supplies existence via lying over. The node's five proof steps are all
included in the declaration docstring. No statement dispute or correction was needed.

Searches performed through `msearch.py H1 lem-weil-pbc-radicial-prime-unique-degree-p`:

- leanfinder: `In R[X]/(X^p-f) in characteristic p every element has p-th power in R
  and each prime has exactly one prime above it`: eight hits including
  `PerfectClosure.isPRadical`, `IsPurelyInseparable.isPRadical`, and Frobenius/perfect
  closure results; none states the three clauses for this quotient.
- loogle: `AdjoinRoot, Algebra.IsIntegral, Ideal.comap`: zero hits.
- grep: `X_pow_sub_C|X \^ p - C|isHomeomorph_comap`, subdirectory `RingTheory`:
  eighteen hits; `PrimeSpectrum.isHomeomorph_comap` generalizes clause (3) conditional
  on a power-in-range property and nilpotent kernel, without clauses (1) and (2).
  Other hits concern cyclotomic polynomials, roots of unity, and integral closure.
- leansearch: `AdjoinRoot X^p minus C f characteristic p integral unique prime lying over`:
  service unavailable (Internal Server Error); no absence claim from this search.
- `rg -n 'radicial|prime_unique|X \^ p - C|AdjoinRoot.*IsDomain'` over both
  `WeilConjectures` and `lean/Sheaf`: found a semilinear-Frobenius polynomial,
  completion quotient statements, and `purelyInseparable_integral_prime_unique`.
  Read that last module: it needs a normal base and purely inseparable fraction-field
  data, and only concludes prime uniqueness; it is not this statement.
- `grep -rn 'lem-weil-pbc-radicial-prime-unique-degree-p' WeilConjectures`: no hits.
- `rg -n 'radicial_prime_unique_degree_p|radicialPrimeUniqueDegreeP'` in Mathlib,
  WeilConjectures, and `dag/lean_names_upstream.json`: no existing declaration with
  the proposed name.

Validation: server single-file compilation and the delivery dry run are run on the
sandbox module. The independent second reader supplies their own reading and delivers;
this worker does not write a second-reading section or push.


## Second reading by H1

Independent second reader: I opened the item node, its five proof steps, its two
statement-dependency nodes, their Mathlib declarations, and the delivered module.
There is no `statement_change`, new node, or dependency module in this delivery.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. Prime number p: `(p : ℕ) (hp : p.Prime)`. The primality hypothesis is explicit,
   with no extra characteristic instance supplied by the caller.
2. Integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`. Commutativity and
   nontriviality are exactly those of the node's integral domain.
3. The vanishing p = 0 in R: `(hchar : (p : R) = 0)`. This is the natural-number
   cast in the base ring, not a claim about the polynomial variable.
4. Element f of that same R: `(f : R)`.
5. The specific quotient C = R[z]/(z^p-f): `AdjoinRoot (X ^ p - C f)` throughout.
   I read `AdjoinRoot` in Mathlib/RingTheory/AdjoinRoot.lean: it is literally the
   quotient of `Polynomial R` by `Ideal.span {X ^ p - C f}`. Here `C f` is
   Polynomial.C, not another quotient or a freely chosen algebra.
6. C is a domain: `[IsDomain (AdjoinRoot (X ^ p - C f))]`. Exactly the node's
   additional assumption. Although unnecessary for this elementary lemma, neither
   domain assumption is removed, and neither is replaced with normality.
7. Clause (1), injectivity: `Function.Injective (of (X ^ p - C f))`.
   I read `AdjoinRoot.of`: the quotient homomorphism composed with Polynomial.C,
   hence precisely the structure map mentioned by the node.
8. Clause (1), integrality: `∀ c : AdjoinRoot (X ^ p - C f), IsIntegral R c`.
   I read IsIntegral and RingHom.IsIntegralElem in IntegralClosure/IsIntegral/Defs:
   existence of a monic polynomial vanishing under evaluation via algebraMap.
   AdjoinRoot.algebraMap_eq identifies that map with `of`, so this clause uses
   the same structure map as injectivity and contraction. No independent Algebra
   instance, field-of-fractions hypothesis, or finite-module hypothesis appears.
9. Clause (2): `∀ c : AdjoinRoot (X ^ p - C f),
   c ^ p ∈ (of (X ^ p - C f)).range`. Every element's actual p-th power lies
   in the image, rather than an unspecified positive power or a p-power iterate.
10. Clause (3), all base primes: `∀ P : Ideal R, P.IsPrime → ...`.
    Ideal.IsPrime means a proper ideal satisfying the prime product condition.
11. Clause (3), existence and uniqueness: `∃! Q : Ideal (AdjoinRoot (X ^ p - C f)),
    Q.IsPrime ∧ Q.comap (of (X ^ p - C f)) = P`.
    I read Ideal.comap in Ideal/Maps: its carrier is the inverse image.
    The unique ideal is quantified subject to both primality and contraction;
    uniqueness does not range over nonprime ideals. Each P has its own Q, with
    no swapped quantifiers. The conjunction contains all three node clauses.

Dependency reading: def-weil-polynomial-ring records `Polynomial`, whose source
structure wraps finitely supported coefficients (AddMonoidAlgebra R ℕ), exactly
one variable over the general commutative ring. def-weil-pbc-integral-closure
records integralClosure, IsIntegral, and IsIntegrallyClosedIn. I read their
sources: integralClosure has carrier `{r | IsIntegral R r}` and algebraMap_mem;
IsIntegrallyClosedIn is the integral-closure predicate. Only the integral-element
part is needed here, using its recorded module. Both dependency records are
usable; no missing notion or private replacement warrants a new node or module.

Source reading: local Stacks .tex files are absent, so I independently opened the
official [07PR](https://stacks.math.columbia.edu/tag/07PR),
[0BR8](https://stacks.math.columbia.edu/tag/0BR8), and
[00GQ](https://stacks.math.columbia.edu/tag/00GQ) pages.
07PR constructs B[z]/(z^p-f) inside the degree-p purely inseparable step, with
B a domain of characteristic p and C a domain with fraction field L. Its other
ambient hypotheses concern the larger regularity argument; the node isolates the
root-extension lemma, whose five displayed proof steps require no such ambient
regularity or completion hypothesis. 0BR8 proves prime uniqueness from powers in
the image; 00GQ supplies surjectivity for an integral injective extension. The Lean
makes exactly the node's isolated claim. Its docstring retains the five steps:
monic quotient basis and integrality; Frobenius additivity; polynomial expansion
and z^p=f; uniqueness by contracting p-th powers; existence by lying over. Sources,
blueprint tags and proof-dependency names are present.

Edge cases: p = 0 and p = 1 are excluded by primality, and characteristic zero
and the zero base ring are excluded by the stated hypotheses. The quotient zero
ring is also excluded by its stated domain hypothesis. f = 0 or a p-th power in R
makes the positive-degree quotient nonreduced and is correctly excluded by that
same hypothesis. For a field base with a domain quotient both rings are fields
and (0) has its unique prime above it, consistent with the signature. There is no
index set or scheme, hence no empty-index or empty-scheme restriction to add.
`universe u` is bound explicitly; the quotient and its ideals naturally live over
R, with no unrelated smaller universe and no unbound variable. No Noetherian,
perfectness, algebraic-closure, or finite-type assumption has slipped in.

Independent searches (using different wording from the first worker):

- `msearch.py ... leanfinder "adjoining a pth root to a domain in positive
  characteristic gives integral injective extension and unique primes"`: eight
  hits, including IsPurelyInseparable.isPRadical, its converse, and
  PerfectClosure.isPRadical. These concern field extensions or perfect closures,
  not this quotient and its conjunction of three conclusions.
- `msearch.py ... leansearch "For a prime p zero in R, AdjoinRoot of X^p-a has
  pth powers in the image of R and bijective prime spectrum"`: unavailable,
  Internal Server Error; no absence conclusion drawn from that service.
- `rg` for `radicial`, `purelyInseparable_integral_prime_unique`,
  `root_X_pow_sub_C_pow`, `isHomeomorph_comap`, and `pow.*mem.*range` in the
  project's lean/Sheaf, source WeilConjectures, and relevant Mathlib files.
  I opened PrimeSpectrum.isHomeomorph_comap: it assumes the power-range property
  and nilpotent kernel and only supplies the spectrum conclusion. I opened
  root_X_pow_sub_C_pow in FieldTheory/KummerPolynomial: it concerns the chosen
  root over a field, not arbitrary elements over R. I opened the project's
  PurelyInseparableIntegralPrimeUnique module: it adds normality and finite
  fraction-field data and only asserts prime uniqueness. None is the item.
- `rg` for both proposed snake-case and camel-case declaration names over all
  Mathlib, source WeilConjectures, project Lean, and dag/lean_names_upstream.json:
  no collision. Existing foundational notions are reused, with no definitions
  or auxiliary theorems in the delivery.

Mismatches and repairs: none. The module and node signature are unchanged; this
second-reading section is the only addition. I mechanically checked exact equality
of lean.statement to the file's signature and the 100-character line limit.
The only theorem has proof `by sorry`; there are no hollow definitions or proved
lemmas. Server scompile completed with exit code 0, no warnings or errors (1.6 s).
The first compile invocation used a path relative to the read-only repository;
using the absolute sandbox path corrected that invocation without changing a tool.
