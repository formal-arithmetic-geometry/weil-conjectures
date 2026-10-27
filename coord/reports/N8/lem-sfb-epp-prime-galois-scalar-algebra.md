## Worker report

The module `Sheaf.FieldTheory.PrimeGaloisScalarAlgebra` states
`Algebra.TensorProduct.prime_galois_scalar_algebra`, with its proof `sorry`.
It introduces no definition, new DAG node, or dependency repair. The original node
statement, dependencies, and proof plan are unchanged.

Clause-by-clause correspondence:

- The three fields are `(F : Type u) (E : Type v) (L : Type w)` with the three
  `[Field ...]` instances. The universes are independent and explicitly declared.
- The field extension `E/F` is `[Algebra F E]`, and the arbitrary extension `L/F`
  is `[Algebra F L]`. These are the recorded field-extension notion; the scalar
  maps are their `algebraMap`s. No embedding into a common overfield is assumed.
- Finiteness of `E/F` is `[FiniteDimensional F E]`.
- Galoisness is `[IsGalois F E]`. Its two fields are precisely
  `Algebra.IsSeparable F E` and `Normal F E`. The former is the recorded separable
  algebraic extension notion. Mathlib normality says that each minimal polynomial
  splits, equivalent here to the node's irreducible-polynomial-with-a-root formulation.
- The prime number is `(p : ℕ) (hp : p.Prime)`; the degree hypothesis is
  `(hdegree : Module.finrank F E = p)`.
- The ring in the conclusion is exactly `E ⊗[F] L`, using the recorded
  `TensorProduct` and Mathlib's tensor commutative ring operations.
- Reducedness is the first conjunct `IsReduced (E ⊗[F] L)`. Its defining property
  is `∀ x, IsNilpotent x → x = 0`, exactly the node's definition of reduced.
- The alternatives form an `Or`. The first is `∃ h : IsField (E ⊗[F] L), ...`;
  `h.toField` supplies inverses on the existing tensor ring, preserving its
  addition and multiplication. The explicit `@IsGalois` uses that field structure
  and `rightAlgebra (R := F) (A := E) (B := L)`.
- The degree of that field over `L` is the `@Module.finrank` equality to `p`,
  with the module coming from that same `rightAlgebra`.
- The second alternative is `Nonempty (@AlgEquiv L (E ⊗[F] L) (Fin p → L) ...)`.
  The source algebra instance is again the explicit canonical `rightAlgebra`;
  the target is the pointwise algebra on the product of exactly `p` copies of `L`.
  An equivalence type is placed inside `Nonempty` to state existence propositionally.
- In both alternatives the scalar map is Mathlib's `includeRight`, explicitly
  `l ↦ 1 ⊗ₜ l` (TensorProduct/Basic.lean, `right_algebraMap_apply`). Thus it is the
  canonical scalar map specified in the node, not an existentially chosen algebra
  structure. All explicit `@` arguments avoid a file-local instance or a hidden
  statement `let`.

Statement dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs, including its
  full class signature and algebraMap field; imported transitively through the
  public statement imports.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable. Read its docstring, full class, and implication
  of algebraicity; used through `IsGalois` in Mathlib.FieldTheory.Galois.Basic.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs; used directly with the ring and
  algebra structures of the public Mathlib.RingTheory.TensorProduct.Basic import.

The proof-dependency modules are imported privately where they serve only the
proof plan: Mathlib.LinearAlgebra.Dimension.Constructions (`Module.finrank_baseChange`),
Mathlib.RingTheory.TensorProduct.Finite (`Module.Finite.base_change`),
Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
(`Algebra.isReduced_tensorProduct_of_finiteSeparable`),
Mathlib.RingTheory.Artinian.Module (`IsArtinianRing.of_finite`,
`IsArtinianRing.equivPi`), and
WeilConjectures.AlgebraicGeometry.TensorGaloisPrimeTransitivity
(`Algebra.TensorProduct.exists_comap_eq_of_galois`). The Galois compositum
leaf uses `IsGalois.sup_right` from the already public Galois.Basic module;
its restriction-map clauses use `IntermediateField.restrictRestrictAlgEquivMapHom`
and `IntermediateField.restrictRestrictAlgEquivMapHom_injective` there. Their
signatures and docstrings were read. The theorem docstring gives all six steps
of the node's proof. The transitivity theorem's equal-universe interface can be
applied after lifting fields to a common universe in a future proof; it does not
restrict this statement's universes.

Edge cases checked mathematically before writing:

- `p = 0` and `p = 1` are excluded by primality, as in the source node. In
  particular finrank's zero value for an infinite-dimensional space cannot
  satisfy the positive degree clause in the field alternative.
- `L = F` yields the field alternative, and `L = E` yields the split alternative.
- For the quadratic example `Q(i)/Q`, `L = Q` gives a degree-two field while
  `L = R` gives the field `C`; a field containing `Q(i)` gives the split product.
- A transcendental extension `L/F` is allowed without any finiteness assumption.
- Characteristic `p` is allowed (including cyclic Artin--Schreier examples),
  as are other characteristics; no primitive root of unity is required for
  this general Galois-algebra input.
- Tensor products use independent field universes. The product's index is
  `Fin p`, which has exactly `p` elements. The tensor algebra is nonzero, since
  its base-changed dimension is the positive prime `p`.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: "A prime degree Galois field extension tensor any
  field extension is reduced and either a Galois field of the same degree or a
  split product". Eight hits, including
  `Algebra.TensorProduct.isField_of_isAlgebraic`, `IsGalois`, and
  `IsGalois.of_separable_splitting_field_aux`; none states the dichotomy.
- `msearch.py ... loogle 'IsGalois, TensorProduct'`: zero hits.
- `msearch.py ... grep
  '[Ii]sGalois.*[Tt]ensor|[Tt]ensor.*[Ii]sGalois|rightAlgebra|isField' FieldTheory`:
  24 hits, principally tensor-domain-to-field and unrelated finite-field results;
  no complete dichotomy.
- `rg` for prime/Galois/scalar and Galois/tensor combinations in both
  `lean/WeilConjectures` and `lean/Sheaf`: transitivity and unrelated scalar
  sheaf and Brauer results, no exact statement.
- `grep -rn 'lem-sfb-epp-prime-galois-scalar-algebra' lean/WeilConjectures`:
  no hits. The chosen declaration name was also searched in Mathlib, Sheaf,
  WeilConjectures, and `dag/lean_names_upstream.json`: no existing match.
- Read TensorProduct.Basic's `rightAlgebra` and `includeRight`, so the canonical
  right scalar structure is reused rather than copied.

Source checked: Stacks `more-algebra.tex`, `lemma-make-finite-level` (Tag 09F4),
including the scalar extensions in the second proof paragraph. This general
auxiliary input is broader than that lemma's DVR/Kummer setting, exactly as the
node expressly says. The current latest blueprint's unit and direct-image proof
were read; they do not change the auxiliary node statement. No statement fault
or disputed claim was found. There is no repair note for this item.

Validation: compiled by the prescribed `scompile.py` against the live server.
The only expected diagnostic is the theorem's `sorry` warning.

## Second reading by N8

Worker self-check, not an independent second agent: the dispatcher explicitly
forbids starting agents and assigns the independent reading to the maintainer.
Reopened the node and final module and checked the correspondence above. There
are exactly the field, extension, finite, Galois, prime, and degree hypotheses;
reducedness is outside the disjunction; the two alternatives both use the right
scalar structure; the field degree is over `L`, not over `E` or `F`; the product
has index `Fin p`. No extra assumption on `L`, characteristic, or universe was
introduced. The initial explicit `@IsGalois` argument order was corrected after
the compiler diagnostic, to `L`, its field instance, the tensor type, its induced
field structure, and the canonical right algebra instance. No mathematical
statement correction was needed.
