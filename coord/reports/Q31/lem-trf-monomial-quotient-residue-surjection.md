## Worker report

The module `Sheaf.RingTheory.MonomialQuotientResidueSurjection` states
`AddMonoidAlgebra.monomial_quotient_residue_surjection`. Its sole theorem proof is
`sorry`; the six-step natural-language proof is in its docstring. Three transparent
abbreviations name constructions explicitly introduced by this node:
`monomialSpan I = Ideal.span (AddMonoidAlgebra.of' ℤ P '' I)`,
`monomialQuotient J K = KR / comap(KR.subtype, JR)`, and
`monomialResidueIdeal P A = m.map (algebraMap R A)`. They contain actual data,
use Mathlib's definitions, and introduce no additional independent notion or node.

Source read: the local ILO PDF, Exposé VIII, printed p. 110 (PDF p. 116),
Lemma 3.4.3 and its proof, including the sentence asserting that the sharp monoid
residue ring is a quotient of the monomial-ideal quotient. Also read the current
blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`
`lem-trf-local-term-locality.md` and its proof to check the recorded ancestry.
The auxiliary node makes the elementary coefficient construction explicit.

Hypotheses, in the order of the node:

- A commutative additive cancellative monoid with zero is `(P : Type u)
  [AddCancelCommMonoid P]`. The universe `u` is explicit.
- Sharpness is `hsharp : ∀ x y : P, x + y = 0 → x = 0 ∧ y = 0`.
- `J ⊆ K` is `hJK`, and the closure conditions `J + P ⊆ J` and `K + P ⊆ K`
  are `hJ` and `hK`. The sets have no nonemptiness assumption.
- The exponent is `(p : P)`; `hpK` and `hpJ` say `p ∈ K` and `p ∉ J`.
- `p ∉ K + (P ∖ {0})` is exactly
  `hp : ∀ k ∈ K, ∀ q : P, q ≠ 0 → k + q ≠ p`.

Objects and conclusions, clause by clause:

- `R` is Mathlib's `AddMonoidAlgebra ℤ P`, whose coefficient families are
  finitely supported and whose multiplication is convolution. The monomial
  `e_q` is `AddMonoidAlgebra.of' ℤ P q`, definitionally `single q 1`.
- For every monoid ideal `I`, the first conjunct states
  `r ∈ monomialSpan I ↔ ∀ q, r.coeff q ≠ 0 → q ∈ I`.
  This is precisely the asserted direct-sum description inside `ℤ[P]`.
- The second conjunct supplies `Module.Basis {k : P // k ∈ K \ J} ℤ
  (monomialQuotient J K)`. Its value at each `k` is explicitly the quotient
  class of `e_k`. Membership of `e_k` in `KR` uses Mathlib's `Ideal.subset_span`.
  Pulling `JR` back to the subtype `KR` gives exactly `KR/JR` under `hJK`.
- The existential `ε : R →+* ℤ` and its equation on every `r` say that constant
  coefficient is a ring homomorphism. The next equation gives `RingHom.ker ε = m`.
- The ring isomorphism `e : (R ⧸ m) ≃+* ℤ` is tied to `ε` by its formula on
  every quotient representative, specifying the induced residue isomorphism.
- `φ : monomialQuotient J K →ₛₗ[ε] ℤ` is a semilinear map from the usual
  `R`-module to the usual `ℤ`-module. Its law `φ (a • x) = ε a • φ x` is exactly
  `R`-linearity when `ℤ` carries the action through `ε`. Surjectivity is explicit,
  and `φ (Submodule.Quotient.mk r) = r.val.coeff p` fixes the coefficient map.
- Every commutative ring `A : Type v` and every ring map `f : R →+* A` are
  represented by `[CommRing A] [Algebra R A]`, with `f = algebraMap R A`.
  This is equivalent data: any such `f` supplies `f.toAlgebra`, and no extra
  flatness, injectivity, nonzero, finite-generation or scalar-tower condition occurs.
- `monomialResidueIdeal P A` is the extension of the generated monomial ideal,
  hence exactly `(f(e_q) : q ≠ 0)` in `A`.
- The final existential is an additive homomorphism from the ordinary Mathlib
  tensor product `monomialQuotient J K ⊗[R] A` to `A ⧸ monomialResidueIdeal P A`.
  Its accompanying law is the entire `A`-linearity condition: for every `c` and
  every tensor `x`, `Φ ((LinearMap.lTensor Q (LinearMap.mulLeft R c)) x) = c • Φ x`.
  The displayed tensor operator sends `q ⊗ b` to `q ⊗ (c*b)`; it is the canonical
  right-factor `A`-action, not an arbitrary auxiliary map. Thus an additive map
  with this law is exactly the asserted `A`-linear map. The tensor factors retain
  the node's order. Surjectivity and the formula
  `Φ ([r] ⊗ b) = Ideal.Quotient.mk mA ((r.val.coeff p : A) * b)` are explicit.
  This formula uniquely determines the tensor of the coefficient map followed
  by the canonical residue identification, because pure tensors generate.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product` is a Mathlib node, not a missing Lean record.
  Its match is `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  including its quotient construction and canonical bilinear map `TensorProduct.mk`.
  Read the universal property `TensorProduct.lift`, `lift.tmul`, `ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, and `LinearMap.rTensor`,
  `rTensor_tmul`, `lTensor`, `lTensor_tmul` in `Mathlib.LinearAlgebra.TensorProduct.Map`.
  The module publicly imports `Map`, which exposes these tensor dependencies.
- Supporting existing definitions are `Ideal.span`, `Ideal.map`, `Submodule.comap`,
  `Submodule.Quotient.mk`, `Module.Basis`, `RingHom.ker`, `Ideal.Quotient.mk`, and
  `LinearMap.mulLeft`. Their signatures were read in the corresponding Mathlib files.
  No dependency interface repair is needed.

Edge cases checked before drafting and again after compilation:

- `J = ∅` is allowed and gives the zero denominator; the support clause also
  includes `I = ∅`. There is no nonemptiness binder on either ideal.
- `P = {0}`, `K = P`, `J = ∅`, `p = 0` gives `R = ℤ`, `m = 0` and the identity
  coefficient quotient. Nothing requires a nonzero exponent or nontrivial monoid.
- For `P = ℕ`, `K = {n | d ≤ n}`, `J = {n | d+1 ≤ n}`, `p = d`, the quotient is
  the expected rank-one coefficient module. If `d = 0`, the same statement applies.
- `K = J` and `K = ∅` cannot supply `hpK` and `hpJ`; these are exactly the node's
  excluded cases, not additional restrictions.
- If `mA = ⊤`, or `A` is the zero ring, the target is zero and surjectivity remains
  meaningful. Arbitrary nonflat maps are included.
- Without `hp`, the coefficient map need not be linear: `P = ℕ`, `K = P`, `p = 1`
  would have `(e_1*e_0)_1 = 1` while `ε(e_1) = 0`. The required hypothesis is retained.
- The coefficient-ring universe `v` is independent of the monoid universe `u`.

Searches actually run (all on 2026-10-24):

- `msearch.py ... leanfinder` with query “Coefficient at a minimal monomial exponent
  in a quotient of nested monoid ideals is a surjective semilinear map to integers
  and base changes to the monomial residue quotient”: eight results, including
  `Ideal.quotientToQuotientRangePowQuotSucc_surjective`, `Ideal.toCotangent_surjective`
  and presentation/Weierstrass maps; none states this result.
- `msearch.py ... loogle '"AddMonoidAlgebra", "coeff"'`: twelve results, including
  `AddMonoidAlgebra.coeff`, `coeffEquiv`, `ofCoeff` and coefficient conversion lemmas;
  these supply the underlying notion but no quotient-residue surjection.
- `msearch.py ... leansearch` with query “coefficient of monomial quotient nested
  ideals sharp additive monoid tensor residue surjective”: eight results, including
  `Ideal.qoutMapEquivTensorQout`, tensor quotient formulas and polynomial coefficient
  lemmas; no exact match for this compound statement.
- `msearch.py ... grep 'constantCoeff|[Ii]deal|quotient|[Ss]urjective'
  Algebra/MonoidAlgebra`: ten hits, chiefly the existing support criterion
  `AddMonoidAlgebra.mem_ideal_span_of'_image` in `Mathlib.Algebra.MonoidAlgebra.Ideal`
  (read in full), and coefficient-map surjectivity. None gives the full result.
- `rg` in the project `WeilConjectures/` and `Sheaf/` for monomial, monoid-ideal,
  constant-coefficient, quotient and coefficient-surjectivity terms found related
  material, including `AlgebraicGeometry.logRegular_monomialIdeal_tensor_injective`.
  Read that file: it concerns a log-regular chart and injectivity of an ideal's
  tensor multiplication map, not this general residue quotient.
- Searches for the item id in `WeilConjectures/` and for all four proposed names in
  `WeilConjectures/`, `Sheaf/` and Mathlib's monoid-algebra directory returned no match.
  Also consulted `dag/lean_names_upstream.json`; its monomial hits concern different
  constructions. There is no existing exact declaration to attach.

No statement correction, disputed clause, new node or dependency module is needed.
`scompile.py` compiled both sandbox mode and the delivery's actual module name cleanly
(1.4 s and 1.3 s); only this wrapper was used for compilation.

## Second reading by Q31

I reread the node and the complete compiling module in a separate pass. This is
an explicit self-review; the dispatch brief forbids starting another agent, and
independent review belongs to the maintainer. The rereading checked every binder
and each conjunct against the mapping above. In particular, the quotient denominator
is the inverse image of `JR` in `KR`, the basis values are monomial classes, `ε` is
fixed on every polynomial, the ring isomorphism is the induced one, and the coefficient
map has the action through `ε`. The final scalar law quantifies over all tensors,
not just pure tensors, and includes all `A`-scalars; together with additivity this
is exactly `A`-linearity. Its pure-tensor formula fixes the canonical base change.
The `Algebra` binder ranges over precisely the ring maps in the node. All hypotheses,
including sharpness, the two closure conditions and indecomposability of `p`, remain.
No mathematical mismatch was found. The only drafting repairs were marking the
transparent abbreviations noncomputable for Mathlib's monoid-algebra instance and
specifying the coefficient rings in `Submodule.comap` so Lean inferred the quotient
as a module quotient. No node field outside `lean` was changed.
