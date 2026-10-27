## Worker report

The module `Sheaf.FieldTheory.DiagonalPFormSeparableIsotropyDescent` states
`Algebra.exists_nonzero_diagonal_p_form_zero_of_isSeparable`, with one postponed
proof and no definitions. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- The fields are `(k : Type u) (L : Type v) [Field k] [Field L]`, with independent,
  explicitly declared universes. `[Algebra k L]` is the extension structure;
  its canonical ring map is injective because its domain is a field.
- The algebraic separable extension is `[Algebra.IsSeparable k L]`. Its definition
  in `Mathlib.FieldTheory.Separable` says that every element's minimal polynomial
  is separable, and `Algebra.IsSeparable.isAlgebraic` supplies algebraicity.
  No finiteness, normality, perfectness, or separable-closedness is assumed.
- Prime characteristic is `(p : ℕ) (hp : p.Prime) [CharP k p]`.
  Primality implies positivity; the characteristic of L follows from its field
  extension structure, so no independent characteristic restriction is added.
- The number of terms and its bound are `(n : ℕ) (hn : 1 ≤ n)`.
- The coefficients and nonnegative exponents are `(c : Fin n → k)` and
  `(m : Fin n → ℕ)`. `Fin n` reindexes the paper's 1,...,n as 0,...,n-1.
- The premise `∃ a : Fin n → L, a ≠ 0 ∧ ... = 0` means that a tuple is not
  the pointwise zero tuple and satisfies exactly the displayed diagonal equation.
  The coefficients in L are `algebraMap k L (c i)`. Each exponent is
  `p ^ (m i)` and the sum is over all `i : Fin n`.
- The conclusion `∃ b : Fin n → k, b ≠ 0 ∧ ... = 0` gives the same equation
  with the original coefficients and exponents over k.
- Neither a nonvanishing condition on c nor any equality/order condition on m
  occurs. Thus zero coefficients and unequal exponents remain allowed.

The statement dependency `def-weil-field` is the existing Mathlib `Field`
(`Mathlib.Algebra.Field.Defs`), whose full signature and docstring were read.
The standard notions `Algebra`, `Algebra.IsSeparable`, `CharP`, `Fin`, powers,
and finite sums are reused, not privately reconstructed. Statement imports are
public. The private proof imports provide the recorded declarations for all
proof dependencies:

- `lem-weil-pbc-separable-closure-exists-galois`:
  `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosure.isGalois` and `SeparableClosure`.
- `lem-weil-pbc-separable-extension-embeds-separably-closed`:
  `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed.lift`.
- `lem-weil-pbc-finite-set-in-finite-galois-subextension`:
  `Mathlib.FieldTheory.Galois.GaloisClosure`,
  `FiniteGaloisIntermediateField.adjoin` and `.subset_adjoin`.
- `lem-weil-pbc-finite-galois-fixed-field`:
  `Mathlib.FieldTheory.Galois.Basic`, `IsGalois.mem_range_algebraMap_iff_fixed`.
- `def-weil-ring-frobenius`:
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`, `iterateFrobeniusOfPrime`
  and `iterateFrobeniusOfPrime_apply`.

The natural-language proof in the declaration follows every DAG step: reduction
to a finite Galois extension, strong induction, deletion of a zero coordinate,
normalization at a maximal exponent, a moving automorphism, and Frobenius
subtraction followed by deletion and reinsertion. Conrad Lemma 1.12 was opened
at https://math.stanford.edu/~conrad/papers/appbnew.pdf, printed p.7. The DAG's
finite Galois reduction extends that assertion to the stated algebraic separable
extension. No statement correction or additional node is needed.

Edge cases checked before writing: n=1 forces its coefficient to vanish if the
premise holds; a vanishing coefficient always supplies a base-field coordinate
solution; all zero coefficients permit any nonzero coordinate tuple; m_i=0
means the first power; equal and unequal exponents are both accepted; coordinates
of a nonzero tuple may individually vanish; p=2 is included. n=0 is excluded by
the source's n≥1, and p=0 or 1 are excluded by primality. Trivial extensions and
infinite algebraic separable extensions are included. Fields exclude the zero
ring, as does the node.

Searches made with `msearch.py Q120 lem-sfb-diagonal-p-form-separable-isotropy-descent`:

- LeanFinder: "A diagonal p form with unequal Frobenius powers has a nonzero zero
  over a separable algebraic field extension only if it has a nonzero zero over
  the base field". Eight hits, including trace-form nondegeneracy,
  `IsPurelyInseparable.inseparable`, and `groupCohomology.Hilbert90.aux_ne_zero`;
  none states the multivariable mixed-exponent descent result.
- Loogle: `Algebra.IsSeparable, Finset.sum`. Three hits about traces or embeddings
  and minimal polynomials, none about descent of nontrivial zeros.
- Mathlib grep in FieldTheory: `quasilinear|[Ii]sotrop.*[Ss]eparab|[Ss]eparab.*[Ii]sotrop`.
  No hits.
- LeanSearch: "Diagonal additive p polynomial nontrivial zero descends through
  algebraic separable field extensions". Eight hits about separably closed
  fields and separable univariate polynomials, none exact.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `quasilinear|[Ii]sotrop.*[Ss]eparab|[Ss]eparab.*[Ii]sotrop|diagonal_p_form`:
  no hits. A broader diagonal search found unrelated geometric diagonal results.
- `grep -rn` for the item id in `lean/WeilConjectures`: no hits.
- `rg -n` for the proposed declaration name in `dag/lean_names_upstream.json`
  and Mathlib: no hits.

No disputed statement or dependency-interface fault was found. All delivered
Lean files are checked with the prescribed server compiler; the expected
`sorry` warning is allowed. The maintainer supplies the independent review.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
