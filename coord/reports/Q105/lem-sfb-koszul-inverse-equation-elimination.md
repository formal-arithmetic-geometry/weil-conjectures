## Worker report

The module `Sheaf.RingTheory.KoszulInverseEquationElimination` states
`Ideal.koszulRegular_of_inverse_equation` with proof `sorry`. It introduces no definitions
and changes only the item's `lean` field. No statement correction, new nodes, dependency
repairs, or disputed statements are needed.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 07D1,
`lemma-lci-local`, especially the paragraph from the prime `q_j` to the final `h'`.
The module docstring records the four accepted DAG proof steps: injectivity of `hz-1`,
the explicit square-zero conormal splitting, split-conormal cancellation, and denominator
clearing back to a principal neighbourhood in `A`. Also read the latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), the ancestor context recorded
by the node; its statement and route are not changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring with unrestricted size is `{A : Type u} [CommRing A]`, with `u`
  declared explicitly. There is no Noetherian, finite-generation, or flatness assumption.
- The ideal and prime are `(I q : Ideal A)` and `(hq : q.IsPrime)`.
  The containment `I ⊆ q` is `(hIq : I ≤ q)`.
- The element outside the prime is `(h : A) (hh : h ∉ q)`.
- The one-variable ring `B = A[z]` is `MvPolynomial (Fin 1) A`; `z` is
  `MvPolynomial.X 0`, the coefficient map is `MvPolynomial.C`, and the inverse
  equation is `MvPolynomial.C h * MvPolynomial.X 0 - 1`.
- The ideal `J = IB + (hz-1)` is the supremum
  `I.map MvPolynomial.C ⊔ Ideal.span {MvPolynomial.C h * MvPolynomial.X 0 - 1}`.
- The displayed `q'` is the same expression with `q` replacing `I`, used directly
  in `(hv : v ∉ ...)`, where `(v : MvPolynomial (Fin 1) A)`. No arbitrary prime
  or arbitrary ideal is substituted. Its description as a prime with quotient
  `(A/q)[1/h]` is a consequence of the explicit construction, `hq`, and `hh`,
  rather than a new hypothesis or an additional conclusion.
- The hypothesis's length and tuple are `(e : ℕ) (b : Fin e → Localization.Away v)`.
  Natural-number indexing includes `e = 0` and records exactly finite tuples.
- The generation hypothesis `JB_v = (b_1,...,b_e)` is `hgen`, using
  `Ideal.span (Set.range b) = J.map (algebraMap B (Localization.Away v))`;
  the equality is oriented with the span on the left, with identical content.
- Positive Koszul homology vanishing is
  `(hreg : RingTheory.Sequence.IsKoszulRegular b)`. Its actual definition is
  `∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex ... b).homology i)`.
  For natural degrees `i ≠ 0` is exactly `i > 0`; the complex's negative terms
  are zero by the project's extension convention.
- The conclusion begins `∃ d : A, d ∉ q ∧`, giving the required principal
  neighbourhood, followed by `∃ (r : ℕ) (f : Fin r → Localization.Away d)`.
- Its first conjunct is
  `Ideal.span (Set.range f) = I.map (algebraMap A (Localization.Away d))`,
  exactly `IA_d = (f_1,...,f_r)` with the equality reversed.
- Its second conjunct is `RingTheory.Sequence.IsKoszulRegular f`, giving precisely
  all positive Koszul homology vanishing over `A_d`. No length comparison or
  generation by elements already in `A` is required.
- Every localization uses `Localization.Away` at the displayed element, hence
  powers of that element. There is no localization at a prime in the signature.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (line 82), with its
  finite-monomial definition; `MvPolynomial.algHom_ext` (line 436), the uniqueness
  clause. `MvPolynomial.aeval` and `aeval_X` were read in `MvPolynomial/Eval.lean`
  (lines 593 and 611); evaluation is used only in the natural-language proof.
  The actual signature uses the recorded `MvPolynomial`, `C`, and `X`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away` (line 142)
  is `Localization (Submonoid.powers x)`; the ring/algebra instances come from
  the public import `Mathlib.RingTheory.Localization.Away.Basic`. Its
  `IsLocalization.Away` characterization (line 50) was also read.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, with its full definition and docstring.
  This uses the existing `ExteriorAlgebra.koszulComplex`, not a private copy.
- Proof-only import `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, its actual exterior-power construction and
  contraction differential were read.
- Proof-only import `Sheaf.RingTheory.KoszulSplitConormalCancellation`:
  `Ideal.koszulRegular_quotient_of_split_conormal`, with its full signature and
  docstring. It supplies precisely step 3, including empty tuples and arbitrary rings.

Edge cases checked before writing:

- `I = 0`: the conclusion permits `d = 1`, `r = 0`, and the empty generating tuple.
- `r = 0` and `e = 0` are syntactically admitted. Under the actual hypotheses
  `e = 0` cannot occur: `hz-1` would vanish in the nonzero ring `B_v`, whereas
  it remains a nonzerodivisor there. No artificial positive-length bound is added.
- `h` may be a zero divisor in `A`: the coefficient recursion for `hz-1` uses
  its constant coefficient `-1`, so it does not require `h` regular or a unit.
- The zero ring and `I = ⊤` are not excluded by new assumptions; the specified
  prime containing `I` already rules them out. Arbitrary characteristics and
  non-Noetherian rings remain covered, with no global finite generation of `I`.

Searches actually run through `msearch.py Q105 lem-sfb-koszul-inverse-equation-elimination`:

- LeanFinder query: `For an ideal I in a commutative ring A, local Koszul regular
  generators of (I,h*z-1) in A[z] near (q,h*z-1) imply local Koszul regular
  generators of I near q`. Eight hits: weak regular sequence localization,
  `Algebra.Generators.ker_localizationAway`, and smooth-locus statements. None
  states the required Koszul-regular inverse-equation elimination.
- Loogle query: `"IsKoszulRegular"`. Successful search, zero hits.
- Grep query: `Koszul|koszul|inverse.*equation`, restricted to Mathlib `RingTheory`.
  One hit, `Regular/RegularSequence.lean:21`, listing Koszul regularity as TODO.
- LeanSearch query: `Removing an inverse equation hz-1 from an ideal generated locally
  by a Koszul regular sequence over an arbitrary commutative ring`. Eight hits:
  fractional ideal inverses and ordinary regular-sequence localization. No exact match.
- Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for
  `inverse.*equation|koszulRegular.*(inverse|polynomial)|koszul.*inverse`, then the
  more selective case-insensitive
  `koszul.{0,80}(inverse|eliminat)|(inverse|eliminat).{0,80}koszul`, found only
  unrelated inverse maps, Koszul signs, and completion statements.
- Direct node-id search in `lean/WeilConjectures` found no occurrence of
  `lem-sfb-koszul-inverse-equation-elimination`.
- Direct name searches for `koszulRegular_of_inverse_equation` and
  `KoszulInverseEquationElimination` in Mathlib, both source roots, and
  `dag/lean_names_upstream.json` found no occurrence. The broader upstream-name
  pattern `koszul.*[Ii]nverse|koszulRegular.*[Ee]limination` also had no hit.

Validation: the prescribed `scompile.py` compiled the module in sandbox and library
module modes with no errors and no non-sorry warnings. All variables are explicitly
bound; `set_option autoImplicit false` enforces that. The JSON signature is extracted
verbatim from the theorem header; only `lean` differs from the base node.

## Second reading by Q105

I reread the complete node, the delivered theorem, and the definitions it uses after
writing them. This is the author's second pass; the dispatcher explicitly forbids
starting another agent, and the maintainer performs the independent review.

The binders match the arbitrary commutative ring, ideal, containing prime, and
nonmember `h`; the actual one-variable polynomial expressions match both `J` and
`q'`. The tuple `b` is in `B_v`, its span equals the extended ideal, and its
Koszul-regularity uses the recorded definition. The conclusion quantifies `d ∉ q`
and a finite tuple in `A_d`, then requires exactly generation and Koszul-regularity.
In particular no finite generation of `I`, Noetherian condition, flatness,
nonempty tuple, or prescribed generator choice has entered the statement.
The natural-number homology convention covers exactly the stated positive degrees.
The explanatory primality and quotient description of `q'` do not introduce
an additional assumption. No mismatch was found, and no correction was made.
