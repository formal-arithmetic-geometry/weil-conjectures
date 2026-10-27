## Worker report

The module Sheaf.RingTheory.FrobeniusSkewLeftMultipleDivision states
SkewPolynomial.exists_frobenius_left_multiple_division, with a single sorry proof.
It reuses Mathlib's skew-polynomial construction and does not introduce any definition.
The node's statement, dependencies and proof are unchanged.

Clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`, at an arbitrary explicitly bound universe u.
- Prime characteristic p > 0: `(p : ℕ) [Fact (Nat.Prime p)] [CharP k p]`.
  Primality includes positivity, so no separate positivity assumption is needed.
- A is the ring of finite sums with coefficientwise addition: `SkewPolynomial k`,
  Mathlib's abbreviation for `SkewMonoidAlgebra k (Multiplicative ℕ)`, whose
  coefficients are finitely supported. Its ring instance is supplied by the action.
- The specified multiplication: `[MulSemiringAction (Multiplicative ℕ) k]` and
  `(hF : ∀ a : k, SkewPolynomial.φ a = a ^ p)`. These specify the ring in the node,
  rather than assume extra mathematical properties of k. The action is determined
  by its generator: Mathlib `φ_iterate_apply` identifies the degree-i action with
  the i-fold iterate, and `monomial_mul_monomial` gives the coefficient
  `a * (φ^[i] b) = a * b^(p^i)` in degree i+j. In particular this is not an
  unspecified twisting action. The required action exists for every such field:
  pull back RingHom.applyMulSemiringAction along
  `powersHom (k →+* k) (frobenius k p)` using MulSemiringAction.compHom.
  This construction needs no inverse Frobenius and no perfectness.
- Degree of nonzero h is the largest nonzero coefficient index:
  `h.support.sup id`. Mathlib `mem_support_iff` says the support consists exactly
  of indices with nonzero coefficient; a nonzero finite polynomial has nonempty
  support. The support supremum therefore is the maximum required in the node.
- Every f,g with g nonzero: `(f g : SkewPolynomial k) (hg : g ≠ 0)`.
- Existence of q,r in A: `∃ q r : SkewPolynomial k`.
- Left multiplication: `f = q * g + r`, with q on the left of g.
- Remainder condition: `r = 0 ∨ r.support.sup id < g.support.sup id`.
  The first alternative handles zero without requiring a degree convention for it.
- No perfectness hypothesis: neither PerfectRing, algebraic closedness,
  bijectivity nor surjectivity of φ occurs. Uniqueness is not asserted, since
  the node asks only existence even though Milne proves uniqueness as well.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, full class at line 180;
  its CommRing and DivisionRing parents give the nontrivial field and inverse.
- def-pc-field-characteristic: `CharP`, Mathlib.Algebra.CharP.Defs, class at line 46,
  with cast_eq_zero_iff; ringChar and ringChar.spec were also read. The explicit
  characteristic binder uses CharP as recorded by the dependency's mathlib_match.
- Mathlib.Algebra.SkewPolynomial.Basic: SkewPolynomial, support, coeff,
  mem_support_iff, φ, φ_iterate_apply, monomial_mul_monomial and instRing.
  The module documentation explicitly describes the action representation.
  These provide the ring already described internally by the node.

The entire four-step natural-language proof is in the theorem docstring: induction
on N(f), leading coefficient cancellation by c = a/(b^(p^(n-m))), degree drop
including n=0, and assembly of q = u+q₁. The only proof dependency is the field
node; its Mathlib module is already a public statement import.

Source check: read the local PDF with pdftotext, PDF page 308 = printed p.296.
The paragraph immediately before Proposition 14.50 states f=qg+r with no
perfectness assumption. The final paragraph of that page separately adds
perfectness for f=gq+r. This distinction matches both the node and the Lean.

Edge cases checked before writing: f=0 admits q=r=0; degree f below degree g
admits q=0,r=f; a nonzero constant g has degree zero, forcing r=0; n=m=0
is handled by cancellation of the only coefficient. The prime binder admits p=2
and excludes p=0 and p=1 as required. Over the imperfect field F_p(t), g=tF
and f=F² give q=t^(-p)F and r=0: no root extraction is needed. All polynomial
supports are finite without restricting their size, and the universe is arbitrary.

Searches for an existing statement (all through the prescribed msearch wrapper
where applicable, group Q23, this item, 2026-10-24):

- leanfinder: "Division with remainder f = q*g + r in a Frobenius skew polynomial
  ring over any field of prime characteristic without perfectness". Eight hits
  concern Witt vectors and perfect closure; none states this division theorem.
- loogle: `"SkewPolynomial"`. Twelve hits include SkewPolynomial, support, coeff,
  φ and instRing, which are reused; none states division with remainder.
- grep: `div|mod|degree|frobenius`, subdirectory Algebra/SkewPolynomial. Five hits
  are module/documentation lines; no division theorem is defined.
- leansearch: "Division with remainder by left multiples in the Frobenius skew
  polynomial ring over a field without assuming perfectness". Eight hits give
  ordinary Polynomial division, divByMonic and related lemmas, not twisted division.
- rg over lean/WeilConjectures and lean/Sheaf for Frobenius/skew combinations and
  SkewPolynomial, plus an item-id search of WeilConjectures. Only the related
  Sheaf.RingTheory.SkewPolynomialTwoSidedDivision supplies a division theorem;
  its full signature and docstring were read. It assumes a bijective twist and
  therefore does not cover the imperfect fields required here. No upstream
  declaration names this item. Searched dag/lean_names_upstream.json as well.
- rg of dag/nodes for Frobenius skew / SkewPolynomial found the existing algebra
  nodes, including the two-sided division and free-submodule consumers, but no
  separate definition missing from this statement. No new notion is needed.

Compilation: scompile.py checked the delivered module in sandbox and library
contexts successfully (1.0 s and 0.9 s), with no errors or warnings.
No statement dispute, correction, new node or dependency repair is needed.

## Second reading by Q23

This is a self-check; the dispatch brief reserves independent review for the
maintainer and prohibits starting another agent. Reopened the node and the
completed Lean file and checked each binder and conclusion as listed above.
The action generator condition exactly specifies the node's Frobenius product;
it imposes no additional field condition. The natural support supremum is used
only for nonzero polynomials in the meaningful remainder alternative, so zero
and constant divisors are covered. The quotient remains on the left. The
related theorem with a bijective twist cannot be reused. No mismatch or change
was found during this rereading.
