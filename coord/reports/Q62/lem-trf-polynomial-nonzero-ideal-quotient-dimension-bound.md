## Worker report

The module `Sheaf.RingTheory.PolynomialNonzeroIdealQuotientDimensionBound` states
`MvPolynomial.ringKrullDim_quotient_le_pred_of_exists_mem_ne_zero`. Its sole proof
is `sorry`, as required for stage 2. The declaration docstring records all five
proof steps of the DAG node. There are no new definitions, helper theorems,
new nodes, dependency repairs, or statement corrections. Only the item's `lean`
field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Let k be a field | `(k : Type u) [Field k]`, with explicitly declared `universe u` |
| Let n >= 1 be an integer | `(n : ℕ) (hn : 1 ≤ n)`; natural numbers with this bound encode exactly the positive integers |
| P = k[t_1,...,t_n] | `MvPolynomial (Fin n) k`; `Fin n` labels exactly n indeterminates, with harmless zero-based labels |
| I is an ideal of P | `(I : Ideal (MvPolynomial (Fin n) k))` |
| I contains a nonzero element | `(hI : ∃ f : MvPolynomial (Fin n) k, f ∈ I ∧ f ≠ 0)` |
| R = P/I | The quotient type `MvPolynomial (Fin n) k ⧸ I` occurs directly in the conclusion; no separate ring or identification hypothesis is introduced |
| dim is ring Krull dimension | The recorded Mathlib declaration `ringKrullDim`, valued in `WithBot ℕ∞` |
| dim R <= n-1 | `ringKrullDim (MvPolynomial (Fin n) k ⧸ I) ≤ ((n - 1 : ℕ) : WithBot ℕ∞)`; subtraction is computed in ℕ before casting |
| I=P is allowed and dim(0)=-infinity | No properness or nontrivial quotient hypothesis; the existing `ringKrullDim` definition gives bottom for the zero quotient |

Statement dependencies were read with their full records and source declarations:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`; its recorded universal-property declarations are
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` and
  `MvPolynomial.algHom_ext` in `Mathlib.Algebra.MvPolynomial.Basic`. The statement
  needs only the polynomial carrier and its existing commutative ring structure.
- `def-weil-pbc-algebra-hom-quotient`: its Mathlib match is used directly, as
  permitted for a Mathlib leaf without a `lean` record. `AlgHom` is in
  `Mathlib.Algebra.Algebra.Hom`; `Ideal.Quotient.algebra` and
  `Ideal.Quotient.mkₐ` are in `Mathlib.RingTheory.Ideal.Quotient.Operations`.
  The statement uses the existing quotient type and inherited ring structure.
  Publicly importing Operations supplies that interface without making a copy.
- `def-weil-pbc-krull-dimension-ring`:
  `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.

Proof dependencies are imported privately where they are not already statement
imports: `Mathlib.RingTheory.Noetherian.Defs` (`IsNoetherianRing`),
`Mathlib.RingTheory.KrullDimension.Polynomial`
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`, the match of
`lem-sf-noetherian-polynomial-dimension`), and
`Mathlib.RingTheory.KrullDimension.NonZeroDivisors`
(`ringKrullDim_succ_le_of_surjective`, the recorded declaration of
`lem-trf-surjective-kernel-nonzerodivisor-dimension-drop`). The domain instance
`MvPolynomial.instIsDomainOfIsCancelAdd`, matching
`lem-weil-pbc-polynomial-ring-domain`, is supplied by the public Basic import.
The remaining proof dependencies are the quotient and dimension nodes already
publicly imported. No dependency import is omitted.

Source check: read Stacks `algebra.tex`,
`lemma-finite-type-domain-over-valuation-ring-dim-fibres` (Tag 00QK), including
its final nonzero residue-polynomial kernel inference. The node isolates the
polynomial-source quotient dimension estimate needed for that inference.

Edge cases checked mathematically before writing:

- `I = ⊤`: contains 1, since a field and its polynomial ring are nontrivial;
  its quotient has dimension bottom, so the bound holds. This case is included.
- `n = 1`, `I = (t_1)`: quotient is k and dimension 0, attaining the bound.
  Every other nonzero proper ideal of k[t_1] likewise gives dimension 0.
- `n >= 1`, `I = (t_1)`: quotient is a polynomial ring in n-1 variables,
  again attaining the bound. Thus the numerical conclusion is sharp.
- For n=2, `I=(t_1 t_2)` is allowed: the quotient need not be a domain,
  reducedness and primality are not assumed, and its dimension is 1.
- `I=⊥` has no nonzero member and is correctly excluded; otherwise the
  polynomial ring itself would contradict the strict bound.
- `n=0` is excluded exactly by the node's positive-number hypothesis.
- The field is in arbitrary universe u and can have any characteristic;
  no algebraic closure, finiteness, or characteristic assumption is added.

Searches for existing declarations (2026-10-24):

- `msearch.py grep` query `ringKrullDim.*quotient|quotient.*ringKrullDim` in `RingTheory/KrullDimension`: 17 hits; examples: `Mathlib/RingTheory/KrullDimension/Regular.lean`, `Mathlib/RingTheory/KrullDimension/Regular.lean`, `Mathlib/RingTheory/KrullDimension/Regular.lean`, `Mathlib/RingTheory/KrullDimension/Regular.lean`.
- `msearch.py loogle` query `MvPolynomial, ringKrullDim`: 6 hits; examples: `ringKrullDim_mvPolynomial_of_isEmpty`, `ringKrullDim_mvPolynomial_of_infinite`, `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`, `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial`.
- `msearch.py leanfinder` query `A quotient of a polynomial ring in n variables over a field by an ideal containing a nonzero polynomial has Krull dimension at most n minus one`: 8 hits; examples: `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial`, `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`, `Polynomial.ringKrullDim_le`, `finrank_quotient_span_eq_natDegree_norm`.
- `msearch.py leansearch` query `Krull dimension of a polynomial ring modulo a nonzero ideal is at most the number of variables minus one`: 8 hits; examples: `ringKrullDim_quotient_le`, `Polynomial.ringKrullDim_le`, `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, `Ring.KrullDimLE`.

The semantic and type searches find the general successor inequality, the
polynomial dimension formula, and quotient monotonicity, but no declaration
with this exact positive-n polynomial-ideal bound. Direct `rg` searches for
`ringKrullDim.*quotient|quotient.*ringKrullDim|nonzero.*ideal.*dimension|ringKrullDim.*sub_one`
in `lean/WeilConjectures` and `lean/Sheaf` find the general upstream
`ringKrullDim_quotient_add_one_le_of_ne_bot` and
`ringKrullDim_quotient_lt_of_ne_bot`. Their source and docstrings were read:
they do not compute polynomial dimension or state the n-1 bound, so neither
is an exact match for this node. The quotient results in Mathlib's
NonZeroDivisors and Basic files and the polynomial dimension theorem were
also read in source. The required `grep -rn` for the node id in
`lean/WeilConjectures` returns no occurrence. A search of
`dag/lean_names_upstream.json`, Mathlib, and both project roots finds no
collision with the proposed full declaration name.

Validation: `scompile.py Q62 lem-trf-polynomial-nonzero-ideal-quotient-dimension-bound`
compiled the module both as a sandbox file (1.8 seconds) and under its library
module name (2.3 seconds), without errors or warnings. Every variable is
explicitly bound and `set_option autoImplicit false` is set. No statement
fault or mathematical dispute was found. Independent review is left to the
maintainer, as specified by the dispatcher's direct-delivery brief.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
