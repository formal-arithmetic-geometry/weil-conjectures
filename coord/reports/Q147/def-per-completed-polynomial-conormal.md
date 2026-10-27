## Worker report

The module `Sheaf.RingTheory.CompletedPolynomialConormal` defines
`AlgebraicGeometry.rigJacobianDifferential`, the completed polynomial conormal
map of equation (NL), Stacks Tag 0AJR, used in Tag 0AJU. The node's statement is
unchanged; only its `lean` field is set. No new nodes or dependency modules.

Hypothesis and clause correspondence:

- The arbitrary commutative Noetherian coefficient ring is `{A : Type u}`,
  `[CommRing A]`, `[IsNoetherianRing A]`. The universe is explicit and arbitrary;
  there is no nonzero-ring or completeness assumption on A.
- The ideal and nonnegative number of variables are `(I : Ideal A)` and `(r : ℕ)`.
  The polynomial ring Q is `MvPolynomial (Fin r) A`.
- P is `rigPolynomialCompletion A I r`, an abbreviation for precisely
  `AdicCompletion (I.map (algebraMap A Q)) Q`. It adds no alternative completion
  notion; its algebra structures and polynomial inclusion are Mathlib's.
- `rigPartialDerivative_existsUnique` states the unique A-linear extension,
  using the equation on the canonical `algebraMap Q P` and `MvPolynomial.pderiv`.
  Its second conjunct preserves `(I.map (algebraMap A P)) ^ n` for EVERY `n : ℕ`,
  including zero. This is continuity for the specified adic filtration.
  `rigPartialDerivative` chooses this uniquely determined map, so the postponed
  proof does not leave the object unspecified.
- The continuous Leibniz clause is `rigPartialDerivative_leibniz`.
- An arbitrary ideal of P is `(J : Ideal (rigPolynomialCompletion A I r))`;
  E is the literal quotient `rigPolynomialCompletion A I r ⧸ J`.
- `rigJacobianOnIdeal` sends `f : J` to the function assigning to i the reduction
  of `rigPartialDerivative I r i f` modulo J. `LinearMap.pi` gives the tuple and
  `(Ideal.Quotient.mkₐ A J).toLinearMap` gives the reduction. It is A-linear.
- Mathlib's `J.Cotangent` is J/J²: its defining quotient is J modulo `J • ⊤`.
  The helper `rigJacobianOnIdeal_vanishes` states that exact submodule is killed,
  using restriction of scalars to A. This is the node's well-definedness clause.
- `rigJacobianDifferential` is the literal `Submodule.liftQ` of the displayed
  map, using that named vanishing theorem. Thus on `J.toCotangent f` its value
  is definitionally `(∂ᵢf mod J)ᵢ`. The finite product `Fin r → E` canonically
  represents the finite direct sum E^{⊕r}; no arbitrary identification is chosen.

Every postponed theorem belongs to a clause of this definition node, is listed
in `lean.declarations`, and has its source, blueprint tag and a complete proof
sketch in its docstring. All three proofs are `sorry`; no definition data or
inline proof is `sorry`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, which means all ideals
  are finitely generated (`isNoetherianRing_iff_ideal_fg`).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; its evaluation and
  uniqueness interfaces `MvPolynomial.aeval` (Eval) and `MvPolynomial.algHom_ext`
  were also read. The completion uses this actual polynomial ring.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, the compatible
  families modulo ideal powers; its Algebra module supplies the ring and
  A-algebra structures, inclusion and `evalOneₐ`. These are reused directly.
- `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv`, the A-derivation.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent`, `Ideal.toCotangent`,
  and the scalar-restriction/quotient interfaces underlying the final map.

Edge cases checked mathematically before writing: r=0 has no derivative indices
and the conormal map has zero target; no positive-r assumption. For I=0 the
completion is Q and these are ordinary polynomial derivatives; for I=A the
completion is the zero ring and uniqueness is automatic. A may itself be the
zero ring. For n=0 the preserved ideal is the entire completion. For J=0 the
source vanishes; for J=P both source and target vanish. Arbitrary proper J,
including non-radical J, is allowed: the Leibniz argument needs only ideal
membership, not reducedness. No characteristic restriction is used.

Searches actually run via `msearch.py Q147 def-per-completed-polynomial-conormal`:

- leanfinder: "Continuous partial derivatives on the ideal-adic completion of a
  polynomial ring and the conormal map from J/J squared to the finite free
  quotient module". Eight results: polynomial-presentation cotangent maps,
  `Ideal.toCotangent_to_quotient_square`, formal-smooth lifting, and extension
  cotangent maps; none defines this completion derivative or its arrow.
- loogle: `AdicCompletion, MvPolynomial.pderiv`: zero hits.
- grep: `AdicCompletion.*(deriv|pderiv)|(deriv|pderiv).*AdicCompletion`: zero hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `rigPolynomialCompletion|rigJacobian|completedConormal|completedPolynomial|CompletedPolynomial`:
  only unrelated trace-formula determinant sections and completed polynomial
  local/test-ring theorems. The earlier module is absent (the node records its
  removal). The proposed declaration names had no existing hits.
- Direct grep of the item's id in `lean/WeilConjectures` and rg in
  `dag/lean_names_upstream.json`: no matches.
- A broader derivation/completion search found
  `Derivation.exists_completion_and_unique_localization` in
  `WeilConjectures.RingTheory.Derivation.CompletionAndLocalization`. Its full
  signature and construction were read: it gives existence of an absolute
  Z-derivation on an arbitrary completion and a shifted-coordinate formula,
  but no canonical A-linear, power-preserving polynomial derivative and no
  conormal arrow. It therefore does not duplicate this notion. The local-ring
  completed polynomial lift calculus theorem likewise uses a different
  completion and base field.

The Stacks source was read locally: restricted.tex equation (NL) defines exactly
[f] ↦ Σ(∂ᵢf)dxᵢ, and Tag 0AJU uses the same completed presentation. No statement
correction or STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py` compiled the module in both sandbox and
library modes, cleanly (4.7 s and 4.5 s); all variables are explicitly bound and
all lines are at most 100 characters. The required delivery dry run follows.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
