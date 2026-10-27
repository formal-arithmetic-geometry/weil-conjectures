## Worker report

Item: `lem-trf-polynomial-regular-sequence-syzygies`, group Q70, stage 2.
The module `Sheaf.RingTheory.PolynomialRegularSequenceSyzygies` states
`RingTheory.Sequence.polynomial_regular_sequence_syzygies`; its sole theorem
has proof `sorry`. There are no new definitions, auxiliary theorems or nodes.
The original node statement, dependencies and accepted proof are unchanged.

Source read: `literature/stacks-project/more-algebra.tex`,
`definition-koszul` and `definition-koszul-complex` (Tags 0622/0623),
`definition-koszul-regular-sequence` (062E),
`lemma-regular-koszul-regular` (062F), and
`lemma-blowup-regular-sequence` (0BIQ), particularly its polynomial-extension
argument. Also read `literature/stacks-project/algebra.tex`,
`definition-regular-sequence` (00LF). The theorem docstring carries all four
accepted proof steps, with their DAG dependencies and coefficientwise argument.

Hypothesis and clause correspondence:

- A commutative ring R is `{R : Type u} [CommRing R]`. The universe `u` is
  explicitly declared; `autoImplicit` is disabled. No field, Noetherian,
  local-ring or domain assumption is introduced.
- The integers s >= 1 and m >= 0 are `(s m : ℕ) (hs : 1 ≤ s)`.
  The natural-number type supplies exactly m >= 0.
- The ordered sequence is `(f : Fin s → R)`, listed in order by `List.ofFn f`.
  `(hf : IsRegular R (List.ofFn f))` uses the recorded regular-sequence
  definition, including successive injectivity and nonzero final quotient.
- S is written directly as `MvPolynomial (Fin m) R`, the recorded polynomial
  ring definition. `MvPolynomial.C (f i)` is precisely the constant polynomial
  associated to f_i. No separate ring or arbitrary map is quantified over.
- The first conjunct is
  `IsRegular (R := MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R)
    (List.ofFn (fun i : Fin s ↦ MvPolynomial.C (f i)))`.
  Both the scalar ring and module are S, so this is regularity in S itself,
  with precisely the same ordered list of constants.
- The second conjunct quantifies over every tuple
  `v : Fin s → MvPolynomial (Fin m) R`, the concrete free module S^s.
  Its standard basis is the existing `Pi.single i 1`; no freeness hypothesis
  or new basis choice is needed. Finite function modules and finitely
  supported free modules coincide through the usual finite-index equivalence.
- Its sole relation hypothesis is
  `(∑ i : Fin s, MvPolynomial.C (f i) * v i) = 0`.
  This is exactly the displayed row-map kernel condition, over S.
- The conclusion existentially quantifies
  `b : Fin s → Fin s → MvPolynomial (Fin m) R` and asserts equality of tuples
  with the double sum over i and over
  `Finset.univ.filter (fun j : Fin s ↦ i < j)`.
  Thus each increasing pair occurs exactly once; no diagonal or reversed
  pair contributes. Values of b on other pairs are irrelevant and may be zero.
- The summand is
  `b i j • (Pi.single j (MvPolynomial.C (f i)) -
    Pi.single i (MvPolynomial.C (f j)))`.
  Since `Pi.single j a = a • Pi.single j 1`, this is exactly
  b_ij(f_i e_j - f_j e_i), with the source sign. The equality is in S^s,
  rather than only in a quotient, span or unspecified isomorphic module.

Recorded statement dependencies read and reused:

- `def-weil-pbc-regular-sequence`: module
  `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular` and its parent `IsWeaklyRegular`.
  Read the full structures and their docstrings (lines 130-147).
- `def-weil-pbc-mv-polynomial-ring`: module
  `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial` and `MvPolynomial.C`.
  Read the polynomial definition and algebra-hom extensionality; also read
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` to verify the
  dependency's universal-property record.
- `def-weil-pbc-free-module`: module
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`.
  Read the basis-existence definition and `free_iff_set`. The tuple module is
  concrete, so the theorem does not add a redundant `Module.Free` hypothesis.
  Also inspected `Mathlib.LinearAlgebra.StdBasis`, whose module documentation
  and `Pi.basisFun_apply` identify standard basis vectors with `Pi.single i 1`.

Recorded proof dependency modules are imported as the stage-3 proof plan:
`WeilConjectures.RingTheory.RegularSequenceKoszulRegular`
(`RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular`,
`IsRegular.isKoszulRegularOn`, `IsRegular.isKoszulRegular`);
`WeilConjectures.RingTheory.KoszulRegularSequence`
(`IsKoszulRegularOn`, `IsH1RegularOn`, `IsKoszulRegular`, `IsH1Regular`);
`WeilConjectures.AlgebraicGeometry.KoszulComplex`
(`ExteriorAlgebra.koszulComplex` and its actual restricted contraction
construction); and
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`
(`HomologicalComplex.homology`). Their source declarations/docstrings and
corresponding DAG records were read. No replacement interface was needed.

Edge cases checked before writing:

- s = 1: there is no increasing pair, so the displayed sum is zero; the kernel
  condition indeed forces v = 0 by injectivity of the single regular element.
- m = 0: `Fin 0` is empty and the polynomial ring consists of constants;
  the theorem reduces to the usual degree-one regular-sequence syzygy result.
- s = 0 is excluded exactly by the node's s >= 1 hypothesis, not by a hidden
  nonempty-index instance. No restriction is placed on m.
- The zero ring and a sequence generating the unit ideal do not satisfy hf,
  because its final quotient must be nonzero. No extra `Nontrivial` instance
  is imposed.
- For s = 2 and f = (x,y) in k[x,y], the generator is (-y,x), confirming the
  sign; arbitrary characteristic, including 2, is allowed.
- Rings with zero divisors remain allowed: the argument concerns successive
  quotient injectivity, not cancellation by every nonzero ring element.

Searches actually run via `msearch.py Q70
lem-trf-polynomial-regular-sequence-syzygies`:

- leanfinder: "A regular sequence remains regular in a polynomial ring and
  every relation among its elements is generated by the pairwise Koszul
  relations". Eight hits: `IsRegular.toIsWeaklyRegular`, `IsRegular`,
  `IsRegular.cons`, `IsWeaklyRegular`, `IsRegular.cons'`,
  `IsRegular.recIterModByRegularWithRing`, `isRegular_cons_iff'`,
  `isRegular_iff`; none states the two-clause theorem.
- loogle: `RingTheory.Sequence.IsRegular, MvPolynomial`. Zero hits.
- leansearch: "A regular sequence over a commutative ring has relations
  generated by the Koszul relations after polynomial extension". Eight
  regularity hits, including `IsRegular.of_faithfullyFlat` and
  `IsRegular.of_faithfullyFlat_of_isBaseChange`; no explicit syzygy theorem.
- grep: `syzyg|[Kk]oszul|IsRegular.of_faithfullyFlat`, Mathlib `RingTheory`.
  Three hits: `Regular/Flat.lean` lines 86 and 92 (preservation of regularity),
  and `Regular/RegularSequence.lean` line 21 (Koszul regularity TODO).
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id, syzygies, polynomial/regular
  sequences and the proposed theorem name found no exact declaration.
  Nearby polynomial-variable regularity and two-variable syzygy results
  concern other statements and do not supply this theorem.

Validation: compiled using the prescribed `scompile.py`; the first attempt
needed the explicit scalar-ring argument in the first conjunct to fix an
ambiguous `MvPolynomial` variable index. This annotation changes no mathematics.
Final compile and delivery preflight outcomes are recorded below after running.

No statement dispute, source error, dependency-interface fault or correction
was found. The maintainer supplies the independent delivery review under the
worker's dispatcher brief; no second worker was started.

Validation outcomes: `scompile.py` compiled both the sandbox statement and its
library module with exit 0 and no warnings. The first `deliver2.py --no-push`
returned `OK (dry run)` at commit `855b29e8e22`: preflight passed and the
module compiled. A final source/JSON check confirmed that only `lean` differs
from the base node, every Lean line is at most 100 characters, all universes
and variables are explicit, and exactly one named theorem proof is postponed.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
