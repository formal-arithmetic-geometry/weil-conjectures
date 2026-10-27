## Worker report

Stage 2, Q140, 2026-10-24. The single module
`Sheaf.RingTheory.DiagonalRootInvariantMonoidAlgebra` states
`RingTheory.diagonal_root_invariant_monoid_algebra`, with its entire proof `sorry`.
No new definitions, axioms, private copies, dependency repairs or statement changes.
Only the assigned node's `lean` record changes.

The statement introduces its intermediate objects as existential witnesses WITH their
exact defining equations, using existing Mathlib notions throughout. In particular,
these are not additional input assumptions. The ideal, root classes, lattice, orthant,
inclusion, integer sublattice, coefficient maps, action and fixed subalgebra are all
uniquely specified. No definition chooses data from a sorried existence theorem.
The isomorphism is specified on every pure tensor, not merely asserted to exist.
There is consequently no missing independent notion requiring a new definition node.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
|---|---|
| Arbitrary commutative ring A | `(A : Type u) [CommRing A]`, explicit universe `u` |
| n at least one | `(n : ℕ) (hn : 1 ≤ n)` |
| n invertible in A | `hnA : IsUnit (n : A)` |
| zeta a unit | `ζ : Aˣ` |
| zeta to the nth power equals one | `hζ : ζ ^ n = 1` in the unit group, equivalently in A |
| All differences for 1 <= a < n invertible | `hsep : ∀ a : ℕ, 1 ≤ a → a < n → IsUnit (1 - (ζ : A) ^ a)` |
| Any r >= 0 | `r : ℕ`, no positivity or nonemptiness requirement |
| Parameters t_1,...,t_r | `t : Fin r → A`, zero-based indexing only |
| Subgroup of (Z/n)^r | `H : AddSubgroup (Fin r → ZMod n)` |

Clause-by-clause correspondence:

| Node | Lean |
|---|---|
| Root ring B | `MvPolynomial (Fin r) A ⧸ I`, with `I = Ideal.span (Set.range (fun i ↦ X i ^ n - C (t i)))` |
| Named roots x_i | `x : Fin r → ... ⧸ I`, and `∀ i, x i = Ideal.Quotient.mk I (MvPolynomial.X i)` |
| P = N^r | `Fin r → ℕ`, with its native additive commutative monoid |
| Rational lattice L | `L : AddSubgroup (Fin r → ℚ)`, with membership iff `∃ a : Fin r → ℤ`, coordinates `a i / n`, and every dot product with h in H vanishes in `ZMod n` |
| Q = L intersect (1/n)N^r | `Q : AddSubmonoid L`, with membership iff every rational coordinate is nonnegative; in L this is exactly the nonnegative numerator condition |
| Literal inclusion P into Q | `ι : (Fin r → ℕ) →+ Q`, with `(ι p).1.1 i = (p i : ℚ)` for every coordinate |
| Fine and saturated | `AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative Q)`; `Multiplicative` only changes notation and uses the recorded dependency's canonical group-completion definition |
| Sharp | `∀ q : Q, IsAddUnit q ↔ q = 0` |
| Q group completion is L | `∃ e : Algebra.GrothendieckAddGroup Q ≃+ L`, with `e (Algebra.GrothendieckAddGroup.of q) = q.1`, so the equivalence extends the actual inclusion |
| Inclusion injective | `Function.Injective ι` |
| nQ contained in P | `∀ q : Q, ∃ p : Fin r → ℕ, n • q = ι p` |
| Integer sublattice Z^r in L | `J : AddSubgroup L`, with membership iff the rational coordinates are an integral tuple |
| Cokernel finite | `Finite (L ⧸ J)` |
| Cokernel annihilated by n | `∀ c : L ⧸ J, n • c = 0` |
| Z[P] and Z[Q] | `AddMonoidAlgebra ℤ (Fin r → ℕ)` and `AddMonoidAlgebra ℤ Q`; these have the free abelian-group monomial bases and additive-exponent convolution product stated by the node |
| Z[P]-algebra structure on A | `α : Algebra (AddMonoidAlgebra ℤ (Fin r → ℕ)) A`, with each basis monomial p sent to `∏ i, t i ^ p i`; this uniquely specifies precisely the map sending each standard generator to t_i |
| Inclusion-induced Z[P]-algebra on Z[Q] | `β : Algebra ... (AddMonoidAlgebra ℤ Q)`, with every `single p 1` sent to `single (ι p) 1` |
| Diagonal H-action fixing A | `σ : Multiplicative H →* (B ≃ₐ[A] B)`; each generator image is exactly `algebraMap A B ((ζ : A) ^ (h.1 i).val) * x i` |
| Residue exponents | `(h.1 i).val` is the canonical representative in 0,...,n-1; `hζ` makes this the prescribed residue-class action |
| Actual invariant algebra B^H | `C : Subalgebra A B`, with `b ∈ C ↔ ∀ h : H, σ (Multiplicative.ofAdd h) b = b` |
| A-algebra isomorphism from the algebra tensor product | `Φ : (A ⊗[AddMonoidAlgebra ℤ (Fin r → ℕ)] AddMonoidAlgebra ℤ Q) ≃ₐ[A] C`, using the native commutative ring multiplication and left A-algebra structure on the tensor product |
| Formula a tensor z^q maps to a product x_i^(nq_i) | First clause after Φ, coerced into B; exponent is `(((n : ℚ) * q.1.1 i).num.toNat)` |
| Image of 1 tensor z^(e_i) is t_i | Second clause after Φ, with `ι (Pi.single i 1)` and target `algebraMap A C (t i)` |
| c_q^n = product t_i^(nq_i) | Final clause for every `q : Q`, in C itself |

The exponent expression does not round or weaken the equation: lattice membership and
`hn` imply that `n * q_i` is an integer, and orthant membership makes it nonnegative.
Its reduced rational numerator is therefore exactly the intended natural exponent.
Likewise Q is explicitly a submonoid of L, not an unrelated isomorphic abstract monoid.
All tensor structures are the ones supplied by the two existentially bound Algebra
instances and their monomial equations. The action is a homomorphism into A-algebra
automorphisms, not merely a family of unstructured functions.

Dependency declarations read and used:

- `def-trf-fs-log-blowup`: public import
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; the monoid predicate it reexports
  is `AlgebraicGeometry.IsFineSaturatedMonoid`, defined in
  `Sheaf.AlgebraicGeometry.LogRegularPair`. Read its complete definition: finite
  generation, injectivity into the canonical Grothendieck group, and saturation there.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; also read `MvPolynomial.algHom_ext` and
  `MvPolynomial.aeval` (`Mathlib.Algebra.MvPolynomial.Eval`).
- `def-weil-pbc-algebra-hom-quotient`: its Mathlib matches `AlgHom`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, and the quotient-ring construction
  in `Mathlib.RingTheory.Ideal.Quotient.Operations` provide precisely the quotient
  algebra used, without an interface repair.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `TensorProduct.lift`, `TensorProduct.ext'`, and pure tensors; read the definition
  and universal-property signatures in `Mathlib.LinearAlgebra.TensorProduct.Defs`
  and `.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: Mathlib matches
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`, `includeRight`,
  `productMap`, `productMap_apply_tmul`, `ext`, in
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`. These supply the native
  multiplication and A-algebra structure used in the signature, as well as the
  proof's prescribed balanced map.
- Proof-only `lem-weil-pbc-free-module-base-change-free`: plain import
  `Mathlib.LinearAlgebra.TensorProduct.Basis`; read `Module.Basis.baseChange` and
  `Module.Basis.baseChange_apply`.
- Proof-only `lem-weil-pbc-monic-quotient-free`: plain import
  `Mathlib.RingTheory.AdjoinRoot`; read `AdjoinRoot.powerBasis'` and the monic
  freeness/finiteness statements. No proof import omitted.

Source checked locally: ILO Exposé IX Proposition 2.1 proof, printed pp.133--134
(PDF pp.139--140), displaying the monoid base change and parameter-root invariant
quotient. The rational-lattice convention is the node's explicit rescaling of this
chart. The latest blueprint ancestor is
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`;
the assigned node is an auxiliary node, not a blueprint unit's own statement.

Edge cases checked before drafting and again against the signature:

- `r = 0`: all tuple types are singleton groups/monoids; products are empty products,
  H is trivial, the tensor quotient and invariant algebra both reduce to A.
- `n = 1`: `ZMod 1` and H are trivial, the separation range is empty, L is the
  integer lattice, Q=P and the quotient generators equal the parameters.
- The zero ring A is allowed: there is no `[Nontrivial A]`; all hypotheses make
  sense and both algebras are zero. The lattice conclusions are independent of A.
- Zero parameters and zero-divisor parameters are permitted; no field, domain,
  regularity, reducedness, Noetherian or parameter-sequence hypothesis occurs.
- H trivial and H the full residue group both have the expected lattice descriptions.
- No hidden small test-object universe, automatic implicit, statement `let`, local
  notation, private definition, or data selected from a `sorry` occurs.

Searches for an existing complete statement (all through the prescribed wrapper
unless stated otherwise):

- `msearch.py ... leanfinder`: "Invariants of a diagonal subgroup action on an algebra
  adjoining nth roots equal the monoid algebra of the nonnegative invariant exponent
  lattice". Eight hits, including `IsGaloisGroup.isInvariant`, general invariant
  algebra results and `FixedPoints.subalgebra`; none includes this parameter-root
  presentation, exponent orthant, fs assertions and canonical base-change formula.
- `msearch.py ... loogle`: "AddMonoidAlgebra, AddSubmonoid, Ideal.Quotient".
  Zero hits; Loogle reports unknown identifier `Ideal.Quotient`.
- `msearch.py ... leansearch`: "invariants of diagonal root algebra are a base change
  of an exponent monoid algebra". Eight hits: general `Algebra.IsInvariant`, root
  pairing material, unramified base change and monoid-algebra congruences; no match.
- `msearch.py ... grep`: `root.*invariant|invariant.*[Ll]attice|diagonal.*[Rr]oot`.
  Twenty-five returned hits in generic invariant representations/root systems;
  no theorem for this algebra and lattice.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `diagonalRoot|rootInvariant|RootInvariant|root.*[Ii]nvariant|invariant.*[Mm]onoid`:
  found strict-local one-variable invariants and root-power-map invariants, and
  `TransverseLocalRootFamilyRegular`, which concerns a different regularity theorem.
  None is this statement. Read the latter's real root-quotient presentation.
- Direct node-id search in `lean/WeilConjectures`: no hits.
- Direct full proposed declaration-name search of Mathlib, both project roots and
  `dag/lean_names_upstream.json`: no declaration-name collision.
- Read related recorded full-compatible-root tower and root-chart definitions:
  these concern whole prime-to-p towers or geometric maps, not a duplicate of the
  theorem. No such auxiliary definition is recreated in this delivery.

Validation: prescribed `scompile.py Q140 lem-per-diagonal-root-invariant-monoid-algebra`
compiled the delivered module both as a sandbox module (4.1 s) and its library module
(8.1 s), with no errors or unexpected warnings. The full eight-step natural-language
proof is in the theorem docstring. No statement dispute or node fault was found.

## Second reading by Q140

A separate rereading pass by this worker compared the node and delivered signature;
no additional agents were started, as the dispatcher brief forbids them. The independent
maintainer review remains separate from this worker's check.

Checked the distinction between Q's canonical Grothendieck group and an arbitrary
abstract group: the equivalence explicitly agrees with the inclusion on each q.
Checked the cokernel against the actual integer lattice J, whose carrier is fixed by
an iff, rather than merely a finite group of unspecified origin. Checked that nQ is
contained in the actual image of the coordinatewise inclusion. Checked that sharp
means only zero is an additive unit. Checked the exact diagonal scaling on every
root, with A-linearity enforced by AlgEquiv, and that C's elements are exactly the
fixed elements. Finally checked all three map clauses individually: pure tensors,
standard parameters, and arbitrary q nth powers, including the integral nonnegative
interpretation of the rational numerator exponent. All node hypotheses and all edge
cases in the worker report appear in the signature. No mismatches required a change.
