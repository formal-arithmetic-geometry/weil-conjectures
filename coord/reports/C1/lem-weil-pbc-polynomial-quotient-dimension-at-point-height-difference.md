## Worker report

The module `Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference` states
`AlgebraicGeometry.topologicalKrullDimAt_polynomial_quotient_eq_height_difference`.
Its sole proof is `sorry`, as required for stage 2. No definition, dependency module,
new node, or statement correction is needed.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`, for every explicitly bound universe u.
- A nonnegative integer n: `(n : ℕ)`, including zero.
- P = k[x_1,...,x_n]: `MvPolynomial (Fin n) k`; the n indices are relabelled 0,...,n-1.
- An arbitrary ideal I of P: `(I : Ideal (MvPolynomial (Fin n) k))`.
- S = P/I and its canonical quotient map π: `MvPolynomial (Fin n) k ⧸ I` and
  `Ideal.Quotient.mk I`. They are explicit terms, rather than independent objects
  with additional presentation hypotheses.
- A prime q of S: `(q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime]`.
- q' = π^{-1}(q): `q.comap (Ideal.Quotient.mk I)`. It is automatically prime
  and contains I; these facts introduce no extra hypotheses.
- Prime heights as suprema of prime-chain lengths: Mathlib's `Ideal.height`.
  Read `Mathlib/RingTheory/Ideal/Height.lean`: for prime ideals it agrees with
  `Order.height` on `PrimeSpectrum` by `PrimeSpectrum.height_eq_orderHeight`.
  Thus it is the same height convention as the node (chains ending below the
  prime have the same supremum as chains ending at it).
- Both heights are finite integers: `∃ h h' : ℕ` with `q.height = (h : ℕ∞)` and
  `(q.comap (Ideal.Quotient.mk I)).height = (h' : ℕ∞)`.
- The full chain of bounds: `0 ≤ h ∧ h ≤ h' ∧ h' ≤ n`.
- The dimension is of the spectrum as a topological space at q, rather than the
  dimension of its local ring: `topologicalKrullDimAt (⟨q, inferInstance⟩ :
  Spec (CommRingCat.of (MvPolynomial (Fin n) k ⧸ I)))`.
- The identity: equality to `((n - h' + h : ℕ) : WithBot ℕ∞)`.
  Since the same conjunction states h' ≤ n, natural subtraction agrees with
  ordinary integer subtraction; no truncation loses information.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`. Also read the recorded universal-property declarations
  `MvPolynomial.algHom_ext` in Basic and `MvPolynomial.aeval` in Eval; the
  statement uses only the polynomial ring itself.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`; also read the recorded `AlgebraicGeometry.Spec.map`.
  `Spec` has underlying space `PrimeSpectrum`, so the prime constructs its point.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`.
  Its body is the infimum over open neighbourhoods of their topological Krull
  dimensions, exactly the recorded definition. No private copy is introduced.

Sources read: the local Stacks TeX file is absent on this machine, so the source
was read at https://stacks.math.columbia.edu/tag/00P2,
https://stacks.math.columbia.edu/tag/00P1, and
https://stacks.math.columbia.edu/tag/00SC. The quotient identity and the polynomial
specialization agree with the node. The declaration docstring carries all seven
proof steps and names their DAG dependencies.

Edge cases checked before writing:

- n = 0: P = k, the only proper ideal is zero; q and q' have height zero,
  and the spectrum at its unique point has dimension zero.
- I = ⊤: the quotient is the zero ring and there is no prime q, so the prime
  binder makes this case vacuous without an added properness hypothesis.
- I = 0: both heights agree, so the identity gives dimension n at every point
  of affine n-space, including nonclosed points.
- A maximal q (a closed point) and a minimal q (possibly nonclosed) use the
  same topological local dimension, not the dimension of S_q. In particular
  a generic point of affine space has height zero but local topological
  dimension n, correctly represented by this statement.
- Nonreduced and reducible quotients are allowed; no domain, reducedness,
  smoothness, algebraic closure, or characteristic assumption is added.
- The height witnesses and h' ≤ n rule out infinite heights and ensure the
  arithmetic formula is faithful. All variables and the universe are explicit.

Searches made for an existing statement:

- `msearch.py ... leansearch "dimension at a point of spectrum quotient polynomial
  algebra height difference"`: service unavailable (Internal Server Error).
  This gives no verdict; the other searches below remain usable.
- `msearch.py ... leanfinder "dimension at a point of spectrum of quotient polynomial
  ring equals number of variables minus height preimage plus height prime"`:
  eight hits, including `height_le_ringKrullDim_quotient_add_spanFinrank`,
  `Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors`,
  `Polynomial.height_eq_height_add_one`, and `ringKrullDim_quotient`.
  These give global dimensions or height bounds, not the requested local
  topological dimension identity.
- `msearch.py ... loogle "Ideal.height, MvPolynomial"`: zero hits.
- `msearch.py ... grep 'topologicalKrullDimAt|height.*MvPolynomial|MvPolynomial.*height'
  RingTheory`: zero hits in Mathlib.
- `rg -n 'topologicalKrullDimAt|lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: the existing local dimension
  definition and smooth relative-dimension results only; none is the quotient
  height-difference formula. The exact node-id search has no hit.
- `rg -n 'height.*quotient|height_difference|quotient.*height' lean/Sheaf` and the
  search for `topologicalKrullDimAt` there: sibling modules mention this node
  in proof docstrings; there is no declaration of this statement. Read the sibling
  `DimensionAtPointLocalRingTrdeg.lean`, whose conclusion is a different identity.
- Read the Mathlib height definition and prime-height equality. The proposed full
  theorem name does not occur in the source or in the project search results.

No node fault or statement dispute was found. Server compile and the delivery dry
run are performed after writing this report; the second reader will write the
independent second-reading section and deliver.

## Second reading by C1

I opened the unit node and the declaration together and checked each introduced
object, hypothesis, and conclusion clause against the source (Stacks Algebra
00P2, with 00P1 and 00SC). The correspondence is:

- The field is Lean `{k : Type u} [Field k]`; this is exactly the node's field and
  has no finiteness, characteristic, or algebraic-closedness assumption.
- The number of variables is `(n : ℕ)`, including `n = 0`, and the polynomial ring
  is `MvPolynomial (Fin n) k`, rendering `P = k[x₁,…,xₙ]`.
- The ideal is `(I : Ideal (MvPolynomial (Fin n) k))`; the quotient is the Lean
  type `MvPolynomial (Fin n) k ⧸ I`, with quotient map `Ideal.Quotient.mk I`.
- The prime is `(q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime]`. The node's
  `q' = π⁻¹(q)` is rendered by `q.comap (Ideal.Quotient.mk I)`; primality and
  containment of `I` are consequences of this binder and map, so no hypothesis is
  omitted or strengthened.
- The existential witnesses `h h' : ℕ` and equalities to `(h : ℕ∞)` and
  `(h' : ℕ∞)` render that both heights are finite. The conjunction
  `0 ≤ h ∧ h ≤ h' ∧ h' ≤ n` renders every stated bound in the node.
- The point is exactly `⟨q, inferInstance⟩` in
  `Spec (CommRingCat.of (MvPolynomial (Fin n) k ⧸ I))`, and the conclusion uses
  the project's `topologicalKrullDimAt`, hence the topological local dimension
  from the node rather than a local-ring dimension.
- The final equality is exactly
  `topologicalKrullDimAt (...) = ((n - h' + h : ℕ) : WithBot ℕ∞)`, including
  natural subtraction and the target coercion.

The source statement 00P2 gives the height difference for a surjection of finite
type algebras; 00P1 supplies the local-dimension formula, and 00SC uses the
specialization `n - height(q') + height(q)`. The Lean declaration's docstring
records all seven proof steps from the node, including residue-field identification,
the polynomial-spectrum dimension `n`, and lifting strict prime chains. No clause
is weaker or stronger than the node.

Edge cases checked independently: `n = 0`; `I = 0`; `I = ⊤` (vacuous because no
prime q exists in the zero quotient); minimal and maximal primes; generic points;
nonreduced and reducible quotients; and arbitrary characteristic. Empty variable
indexing is represented by `Fin 0`, and all universes remain explicit through `u`.

I repeated the existing-definition searches with `rg` over Mathlib, the source
repository, and `lean/Sheaf`, and with the recorded LeanSearch, LeanFinder, and
Loogle queries. Only the three dependency declarations were found:
`MvPolynomial`, `AlgebraicGeometry.Spec`, and `topologicalKrullDimAt`; no theorem
for this height-difference identity exists. The Stacks pages 00P2, 00P1, and 00SC
were opened and agree with the node. There are no new definitions or dependency
modules, and no mismatch required a change.
