## Worker report

The module `Sheaf.RingTheory.KoszulEqualLengthGenerators` states
`RingTheory.Sequence.isKoszulRegular_iff_of_span_eq`, with proof `sorry`.
It states exactly the equal-length generator invariance in Stacks, More on Algebra,
Tag 066A, lemma-independence-of-generators (3). The node is unchanged except for `lean`.
No definitions, helper nodes, dependency repairs, or statement corrections are needed.

Hypothesis and clause correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`, with explicit arbitrary universe `u`.
- A nonnegative length r: `{r : ℕ}`, including zero.
- Two ordered tuples a_1,...,a_r and b_1,...,b_r: `(a b : Fin r → A)`.
  Their identical index type enforces exactly the same length, without any positivity condition.
- Equality of generated ideals: `hspan : Ideal.span (Set.range a) =
  Ideal.span (Set.range b)`. No separate ideal or choice of generating expressions is assumed.
- If a is Koszul-regular, so is b: the forward implication of
  `IsKoszulRegular a ↔ IsKoszulRegular b`.
- Equivalent positive-degree vanishing conditions: the reverse implication gives the stated
  equivalence. The dependency definition `IsKoszulRegular f` is literally
  `∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex A r f).homology i)`.
  Thus no extra comparison map or homology isomorphism is asserted.
- No proper-ideal, local, or Noetherian assumption: none appears among the binders.
  No `Nontrivial A` assumption occurs, so the zero ring is included.

Dependency declarations read and used:

- Statement dependency `def-weil-pbc-koszul-regular-sequence`:
  `WeilConjectures.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular`, whose complete definition and docstring were read.
  Its module is publicly imported; no private copy of Koszul regularity is introduced.
- Ideal generation uses Mathlib `Ideal.span` and `Set.range`, publicly imported through
  `Mathlib.RingTheory.Ideal.Span`.
- Proof dependency `lem-sc-koszul-conormal-basis`:
  `WeilConjectures.RingTheory.KoszulConormalBasis`,
  `ExteriorAlgebra.exists_koszul_conormal_basis`, read with its full signature and proof docstring;
  its module is imported privately for the future proof.
- Proof dependency `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`:
  Mathlib `OrzechProperty.bijective_of_surjective_endomorphism`, read in
  `Mathlib.RingTheory.OrzechProperty`, with `CommRing.orzechProperty` supplied by the privately
  imported `Mathlib.RingTheory.FiniteType`.
- Proof dependency `def-weil-abstract-derived-category`:
  Mathlib `DerivedCategory` and `HasDerivedCategory`, read in and privately imported from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- Proof dependency `lem-sfb-koszul-substitution-unit-mod-ideal` currently has neither a Lean
  record nor a Mathlib match. Its mathematical step is retained explicitly in the proof
  docstring; there is no module to import yet. It is not required to type this statement.

The declaration docstring carries all four node proof steps: conormal basis, coefficient
matrix surjectivity modulo the ideal, the finite-module bijectivity/determinant argument,
and the quasi-isomorphism comparison followed by exchange of the two tuples.

Edge cases checked mathematically before writing:

- r = 0: both tuples are empty, their generated ideals are zero, and both Koszul complexes
  are concentrated in degree zero. The equivalence is true.
- A = 0: all complex terms and homology modules are zero. Both sides are true.
- Unit ideal: a generating tuple of one yields a contractible Koszul complex; no properness
  is needed. The quotient ring used in the proof may itself be zero.
- Zero ideal in a nonzero ring with r > 0: the all-zero tuples have nonzero degree-one
  homology, so both sides are false; the equivalence does not assert universal regularity.
- Nonlocal and non-Noetherian rings are admitted by the same binders and the source proof.

Searches for an existing statement:

- `msearch.py ... leanfinder "Koszul regularity is invariant under equal length change of
  generators of an ideal"`: eight hits on weak/ordinary regular sequences, permutations,
  append, and dimension; none states Koszul-regular generator invariance.
- `msearch.py ... loogle '"Koszul", "span"'`: zero hits.
- `msearch.py ... grep '[Kk]oszul.*(generat|span)|independence.of.generators' RingTheory`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `IsKoszulRegular`, Koszul with
  generator/span patterns, and equal-length patterns found the definition, regular-to-Koszul
  implications, base-change and conormal comparisons, and local generating tuple results;
  none supplies this arbitrary-ring equivalence. The local tuple change result has a local
  ring hypothesis and therefore does not match.
- `grep -rn "lem-sfb-koszul-equal-length-generators" lean/WeilConjectures`: no hits.
- `rg` for the proposed name `isKoszulRegular_iff_of_span_eq` in Mathlib, both project roots,
  and `dag/lean_names_upstream.json`: no hits.

The source statement and its entire proof were read in
`literature/stacks-project/more-algebra.tex`, lines 7711–7755. The source explicitly states
part (3) for an arbitrary ring and an arbitrary ideal. No node fault or disputed statement
was found.

Validation: the required server compile, delivery dry run, and delivery are run with the
prescribed wrappers; expected declaration-uses-sorry warnings alone are permitted.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
