## Worker report

The delivery states `HopfAlgebra.augmentation_monomial_pairing` in
`Sheaf.RingTheory.HopfAlgebra.AugmentationMonomialPairing`. Its sole theorem has
proof `sorry`; there are no new definitions, helper theorems, or axioms. The
accepted Q34 stage-1 split, its natural-language statement, and its proof steps
are preserved. The earlier worker's rejection was from stage-1 `deliver.py`;
`coord/brief-stage2.md` §0 explicitly permits this stage-2 handoff.

The source was read directly with `pdftotext` from
`literature/milne-algebraic-groups_iAG2017.pdf`: Sections 11e, 11.24--11.26,
printed pp.216--218, and Lemma 11.27, printed p.218. In particular Lemma 11.27
states the nonzero-factorial condition and the monomial basis. Its derivative
calculation is used only after evaluation at the counit, as the accepted node
already requires.

Hypotheses and objects, matched individually:

- The field is `(k : Type u) [Field k]`, using the `Field` Mathlib match of
  `def-weil-field`. The algebra carrier has its independent universe
  `(C : Type v)`; `[CommRing C] [HopfAlgebra k C]` provides the commutative
  unital algebra and its structure over k.
- Finite generation as an algebra is `[Algebra.FiniteType k C]`. No finite
  dimension of C, smoothness, reducedness, connectedness, characteristic-zero,
  or algebraic-closure assumption is imposed.
- `HopfAlgebra` bundles exactly the maps and axioms in the node.
  `Bialgebra.comulAlgHom k C` is Delta, `Bialgebra.counitAlgHom k C` is epsilon,
  and `HopfAlgebra.antipode k` is the k-linear S. The inherited `Coalgebra`
  supplies coassociativity and both counit identities; `Bialgebra` supplies
  multiplicativity and preservation of 1; the two fields
  `mul_antipode_rTensor_comul` and `mul_antipode_lTensor_comul` are the two
  antipode equations. These full class declarations and docstrings were read.
  There is no `IsCocomm` assumption.
- The notation “put I = ker epsilon” is rendered by `(I : Ideal C)` and
  `hI : I = RingHom.ker (Bialgebra.counitAlgHom k C)`. This names precisely
  that canonical ideal: for every allowed algebra it can always be instantiated
  with the kernel and `rfl`. It is not an extra restriction on the algebra or
  an arbitrary choice of augmentation.
- The chosen lifts are `(d : ℕ) (x : Fin d → I)`, and their classes form the
  supplied `b : Module.Basis (Fin d) k I.Cotangent` with
  `∀ i, b i = I.toCotangent (x i)`. `Ideal.Cotangent` is Mathlib's actual I/I²,
  with the scalar action inherited from the k-algebra. The type of d permits 0.

Conclusions and conventions, matched individually:

- `FiniteDimensional k I.Cotangent` asserts finite-dimensionality of I/I²
  before any choice of basis.
- `∃! v : Fin d → C →ₗ[k] k, ...` supplies the coordinate functionals rather
  than assuming their existence. The first three conjuncts assert, separately,
  `v i 1 = 0`, vanishing on I², and
  `v i (x j) = if i = j then 1 else 0`. The splitting C = k + I makes those
  conditions determine v uniquely. This is theorem-level existence of the
  specified functionals, not a definition choosing data from a `sorry`.
- The node's convolution is Mathlib's `LinearMap.convMul` on
  `WithConv (C →ₗ[k] k)`. Its defining formula is exactly multiplication in k
  after `TensorProduct.map` and comultiplication. The file was read at lines
  55--68 (multiplication), 174--193 (unit and algebra), and 212 (`convRing`).
- Each `V^a` is written as
  `(List.ofFn (fun i : Fin d ↦ WithConv.toConv (v i) ^ a i)).prod`.
  `List.ofFn` enumerates Fin d increasingly. Consequently its product is the
  ordered v_1^a_1 * ... * v_d^a_d, even for noncocommutative Delta. Zero powers
  and empty list products use the convolution unit, which is epsilon, not
  the constant functional 1. No commutative finite-set convolution product is
  used.
- `∀ n : ℕ, (n.factorial : k) ≠ 0 → ...` has precisely the allowed degrees.
  The basis index is `{a : Fin d → ℕ // ∑ i, a i = n}`. Its target is the
  existing `Ideal.associatedGradedPiece I n`, literally the quotient of I^n
  by the inverse image of I^(n+1) under inclusion. The existential basis B
  is normalized at every index by `B a = Submodule.Quotient.mk ⟨prod, ha⟩`,
  where `prod = ∏ i, (x i : C) ^ a.val i` and `ha : prod ∈ I ^ n`. Thus it is
  the specified monomial basis, not merely an unnamed basis or a dimension
  assertion. Existential membership witnesses avoid introducing any postponed
  well-definedness theorem or private quotient model.
- In that same degree/factorial block, the two degree equalities for a and b
  lead to the exact displayed evaluation: `if a = b then
  ∏ i, (Nat.factorial (a i) : k) else 0`.
- The final conjunct ranges over *every* exponent vector a, outside the
  factorial block. Membership `c ∈ I ^ ((∑ i, a i) + 1)` implies the displayed
  word evaluates to 0. This keeps annihilation in arbitrary degree and
  characteristic, not only degrees where the factorial is nonzero.
- Ideal exponent 0 is the top ideal by Mathlib's powers. Degree-zero indexing
  has the sole zero vector, whose monomial is the empty product 1 and whose
  word is epsilon. If d = 0 and n > 0, the index subtype is empty, so the
  asserted basis is exactly the empty basis of the zero graded piece. These
  clauses are included by the actual indexing and basis normalization, without
  an extra hypothesis excluding any case.

Dependencies used:

- `def-weil-field`: `Field`, from Mathlib (no Lean record is needed for this
  Mathlib leaf).
- Added the already landed `def-weil-pbc-associated-graded-ring` to
  `stmt_deps`, as §5 permits. Its recorded module is
  `WeilConjectures.RingTheory.AssociatedGradedRing`; its declarations include
  `Ideal.associatedGradedPiece`. The complete recorded node, the piece
  definition, and its docstring were read. Its module is publicly imported;
  no duplicate definition is made. There are no dependency-record repairs.
- `lem-sfb-convolution-linear-map-algebra` is a Mathlib proof dependency.
  Its recorded declarations `LinearMap.convRing`, `LinearMap.convAlgebra`,
  `LinearMap.convMul_apply`, `LinearMap.convOne_apply`, and
  `LinearMap.convAlgebraMap_apply` are supplied by
  `Mathlib.RingTheory.Coalgebra.Convolution`, publicly imported transitively by
  `Mathlib.RingTheory.HopfAlgebra.Basic`. These are also used to express the
  statement's convolution words.
- `lem-sfb-bialgebra-counit-word-product-rule` currently has no Lean record
  and is not a statement dependency. It is retained unchanged in `proof_deps`
  and explicitly named in the theorem's full six-step proof docstring. There
  is currently no module for it to import; the maintainer can add its proof
  import after that node is stated. No declaration of that independent lemma
  is silently added to this delivery.

Edge cases checked mathematically and against the Lean signature:

- n = 0: 0! = 1, the only exponent vector is zero, C/I = k, and the
  normalized basis vector is 1. The unit word kills I and evaluates to 1 on 1.
- d = 0: the exponent-vector type has one function, with degree 0. Positive
  degree indices are empty. Since I/I² = 0 implies I = I², all positive
  pieces vanish, exactly as an empty basis requires.
- C = k, the trivial Hopf algebra: I = 0, so the preceding d = 0 case applies.
- In characteristic p, the basis/evaluation block is asserted only when
  n! is nonzero. Annihilation still applies in all degrees. The example
  k[t]/(t^p) with primitive t explains why the factorial condition must stay.
- No cocommutativity assumption was introduced: all convolution factors stay
  in their original increasing order. The G_m example confirms that no
  incorrect global derivative identity from the printed proof is required.
- Independent universes u and v avoid imposing a size equality on k and C.

Searches made (all service queries used the prescribed msearch.py wrapper):

1. LeanFinder: “Factorial pairing between augmentation ideal monomials and
   convolution powers of tangent functionals in a commutative Hopf algebra”.
   Eight hits were antipode/convolution identities and Laurent-polynomial
   comultiplication identities; none states this theorem.
2. Loogle: `HopfAlgebra, Ideal`. One hit,
   `HopfAlgebra.Quotient.instQuotientIdeal`, constructs quotient Hopf algebras;
   its signature and source do not provide the pairing or monomial basis.
3. Mathlib grep: `cotangent|Convolution|convMul` in `RingTheory/Coalgebra`.
   Five hits identify the existing convolution product file and formulas;
   no augmentation monomial theorem.
4. LeanSearch: “A basis of the cotangent space of a Hopf algebra yields a
   monomial basis of augmentation quotients in degrees with invertible
   factorial”. Eight hits include `Polynomial.basisMonomials`,
   `MvPolynomial.basisMonomials`, `Module.Basis.symmetricAlgebra`, and bases
   for presentation cotangent modules. These signatures and the polynomial
   and symmetric-algebra sources were checked: they concern polynomial or
   symmetric algebras themselves, not the augmentation graded pieces of an
   arbitrary Hopf algebra, and do not give the convolution pairing.
5. Project rg searches: augmentation, counit ideals, cotangent, convolution,
   `WithConv`, `HopfAlgebra`, and the item id in `lean/WeilConjectures` and
   `lean/Sheaf`. Existing nearby material concerns augmentation height,
   relative Hopf modules, and associated graded rings. The already defined
   `Ideal.associatedGradedPiece` was found and reused. Exact searches for
   `augmentation_monomial_pairing` and `AugmentationMonomialPairing` in both
   project roots, Mathlib, and `dag/lean_names_upstream.json` found no prior
   declaration. The item-id grep in the upstream root likewise found none.

No statement correction or `STATEMENT-DISPUTED` issue is needed. Only `lean`
and the permitted addition of a landed statement dependency change in the node.

Validation: the prescribed scompile.py compiled the delivered module cleanly
in both sandbox and library module modes (1.2 seconds each), with no errors or
warnings. All variables and universes are explicitly bound, auto-implicits are
disabled, and the maximum Lean line length is 88 characters.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
