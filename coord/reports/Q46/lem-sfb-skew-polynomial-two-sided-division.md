## Worker report

States `SkewPolynomial.exists_two_sided_division` in
`Sheaf.RingTheory.SkewPolynomialTwoSidedDivision`. Its entire proof is `sorry`.
No definition, new DAG node, dependency module, or statement correction is needed.
The accepted stage-1 statement and simultaneous induction proof plan are preserved.

The previous worker's BLOCKED ending was a stage-1 unchanged-split refusal. The
current `coord/brief-stage2.md` §0 explicitly authorizes stating a reviewed split;
the current queue lists this item at stage 2 and its node has no Lean record.
There is no released repair note for this item. This delivery does not re-split it.

Clause-by-clause correspondence:

- “k is a field” is `{k : Type u} [Field k]`, with explicit universe `u`.
  The recorded dependency `def-weil-field` is the Mathlib match `Field`, in
  `Mathlib.Algebra.Field.Defs`. Its signature and docstring were read; it extends
  `CommRing` and `DivisionRing` and includes nontriviality and nonzero inverses.
- “σ is a ring automorphism” is `[MulSemiringAction (Multiplicative ℕ) k]`
  with `(hσ : Function.Bijective (SkewPolynomial.φ (R := k)))`.
  The generator `φ` is already a ring homomorphism, so bijectivity says exactly
  that it is a ring automorphism. This uses the existing Mathlib encoding of an
  endomorphism by a natural-number action, with bijectivity added. It imposes no
  condition beyond the automorphism hypothesis: every σ defines the action
  `(Multiplicative.ofAdd n) • a = σ^[n] a`, and `φ_iterate_apply` identifies every
  given such action with the iterates of its generator. No unrelated choice of
  multiplication or compatibility assumption is introduced.
- The ring A of finite coefficient sums is Mathlib's `SkewPolynomial k`, already
  an abbreviation for `SkewMonoidAlgebra k (Multiplicative ℕ)`. Its underlying
  coefficient functions have finite support; its addition is coefficientwise.
  The ring structure comes from `SkewPolynomial.instRing`. The read signature
  `monomial_mul_monomial` says
  `monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s))`.
  This is precisely the node's multiplication `(aF^i)(bF^j)=aσ^i(b)F^(i+j)`.
- The degree of a nonzero polynomial is written `p.support.sup id`. The read
  definition `SkewPolynomial.support` lists the indices of nonzero coefficients
  (`mem_support_iff`), and `Finset.sup` computes the maximum of the finite set
  with bottom zero. A nonzero polynomial has nonempty support, so this maximum
  is exactly its degree. The node defines degree only for nonzero polynomials;
  giving it the harmless value zero on the zero polynomial does not affect
  either disjunctive remainder bound. No new degree notion is needed.
- “every f,g in A with g≠0” is `(f g : SkewPolynomial k) (hg : g ≠ 0)`.
- The four outputs are `∃ qL rL qR rR : SkewPolynomial k`.
- `f=q_L g+r_L=g q_R+r_R` is the pair of conjuncts
  `f = qL * g + rL ∧ f = g * qR + rR`.
- Each of the two remainder clauses is retained separately, respectively
  `(rL = 0 ∨ rL.support.sup id < g.support.sup id)` and
  `(rR = 0 ∨ rR.support.sup id < g.support.sup id)`.
  There is no uniqueness assertion or additional degree bound.

Dependency and source reading: `def-weil-field` supplies `Field` from
`Mathlib.Algebra.Field.Defs`, publicly imported. All other notions are existing
Mathlib declarations from the publicly imported `Mathlib.Algebra.SkewPolynomial.Basic`:
`SkewPolynomial`, `support`, `φ`, `φ_iterate_apply`, `monomial_mul_monomial`,
and `instRing`. The proof dependency is the same field node, so no extra private
proof import is needed. Also read `MulSemiringAction` and
`MulSemiringAction.toRingHom` in `Mathlib.Algebra.Ring.Action.Basic`, and the
finite supremum definition in `Mathlib.Data.Finset.Lattice.Fold`.

Read the source PDF directly with `pdftotext -f 308 -l 308 -layout`: printed
p.296 places f=qg+r before Proposition 14.50 and f=gq+r after it, with the
second side using that the coefficient endomorphism is an automorphism. The
item generalizes Frobenius to an arbitrary automorphism by exactly the same
coefficient cancellation. Its docstring includes all four recorded proof steps:
zero and small-degree cases; c=a/σ^d(b) on the left; c=σ^(-m)(b^(-1)a) on the
right; strict degree descent and the n=m=0 base case. Read the latest blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md`; this is a supporting algebraic
input in the inherited chain, not a change to its unit statement.

Edge cases checked before writing:

- f=0: take all four outputs zero, without assigning nonzero degree to zero.
- g a nonzero constant: `g.support.sup id=0`, so the strict inequalities cannot
  hold and each remainder must be zero, exactly the field division assertion.
- f nonzero of smaller degree than g: zero quotients and remainders f satisfy
  both bounds. If both degrees are zero, cancellation gives remainder zero.
- σ=id gives ordinary polynomial division. No characteristic or perfectness
  restriction is imposed. The universe u is unrestricted.
- For k=ℂ, σ conjugation, f=F^3, g=iF: qL=-iF^2, qR=iF^2 and zero remainders
  confirm the order of multiplication and both coefficient cancellations.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder "Skew polynomials over a field with an automorphism admit left and right division with smaller degree remainder"`:
  eight ordinary Polynomial division results, no skew division result.
- `msearch.py ... loogle "SkewPolynomial, RingEquiv, MulSemiringAction"`:
  zero hits.
- `msearch.py ... grep "div|degree|natDegree" Algebra/SkewPolynomial`:
  five hits, only documentation of degree/update; no division theorem.
- `msearch.py ... leansearch "Division algorithm for skew polynomial rings whose coefficient endomorphism is bijective"`:
  eight Polynomial or MvPolynomial division results; their central multiplication
  does not give the present statement.
- `rg -n "SkewPolynomial|skewPolynomial|skew_polynomial" lean/WeilConjectures lean/Sheaf`:
  no existing skew-polynomial construction or division statement. A broader
  `skew.polynomial` search finds only the explanatory Lang–Steinberg comment in
  `WeilConjectures/LinearAlgebra/SemilinearFrobenius.lean`.
- `grep -rn "lem-sfb-skew-polynomial-two-sided-division" lean/WeilConjectures`:
  no attachment. `rg` of the upstream declaration index also gives no match.
- Read all of the relevant Mathlib Basic API, in particular its actual definitions
  of support and the twist, rather than assuming that the documentation's
  mentions of `natDegree` refer to an implemented degree declaration.

Validation: `scompile.py Q46 lem-sfb-skew-polynomial-two-sided-division
<module>` passed both the sandbox and library-path checks (2.7 s and 2.9 s).
No auto-bound variable, warning, or error. The only postponed declaration is
`SkewPolynomial.exists_two_sided_division`. No statement dispute or node fault.
The independent second reading is performed by the maintainer as prescribed in
the dispatched brief; this report does not claim to be an independent reading.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
