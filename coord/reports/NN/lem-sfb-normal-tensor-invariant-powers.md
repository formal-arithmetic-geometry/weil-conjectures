## Worker report

The module `Sheaf.FieldTheory.NormalTensorInvariantPowers` states
`Algebra.TensorProduct.exists_pow_eq_scalar_of_normal_invariant` with a single
`sorry` proof. No definition is introduced. The node's statement, dependencies,
proof, and existing historical correction record are preserved verbatim; only
its `lean` field is changed. No repair note for this item is present.

Hypothesis and clause correspondence:

- The fields `K`, `L`, `E` have independent explicit universes `u`, `v`, `w` and
  `[Field K] [Field L] [Field E]`. The two field extensions are exactly
  `[Algebra K L] [Algebra K E]`, using the recorded `Algebra` declaration of
  `def-pc-field-extension`.
- Finite dimension of `E/K` is `[FiniteDimensional K E]`. There is no finite
  dimension assumption on `L/K` and no separability assumption on `E/K`.
- Normality is `[Normal K E]`. The Mathlib class says that the minimal
  polynomial of every element splits over `E` and that the extension is
  algebraic. The latter is already implied by finite dimension here, so this
  adds no hypothesis beyond the node's definition of normality.
- The tensor ring is Mathlib's `L ⊗[K] E`, with its canonical commutative-ring
  structure, unit `1 ⊗ 1`, and multiplication `tmul_mul_tmul`. These are the
  recorded Mathlib declarations of
  `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
- The reduced ring and its element are exactly
  `x : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)`. Mathlib defines `nilradical T`
  as `(0 : Ideal T).radical`, with membership equivalent to nilpotence.
- The scalar map is written explicitly everywhere as
  `l ↦ Ideal.Quotient.mk (nilradical (L ⊗[K] E)) (l ⊗ₜ[K] (1 : E))`.
- The group is the full automorphism group `E ≃ₐ[K] E`. In `hx`, its tensor
  action is precisely `Algebra.TensorProduct.map (AlgHom.id K L) σ.toAlgHom`,
  which sends `l ⊗ e` to `l ⊗ σ(e)` by `map_tmul`.
  The fixedness clause quantifies over each `σ` and every representative `t`
  with quotient image `x`, requiring that the transformed representative has
  quotient image `x` too. This is an explicit rendering of fixedness on the
  reduced ring, not an assumption of fixedness in the unreduced tensor ring.
  Every `x` has a representative by `Ideal.Quotient.mk_surjective`; the
  condition is therefore not vacuous. Ring homomorphisms preserve nilpotents
  (`IsNilpotent.map`), so the tensor maps descend, and quotient images of
  any two representatives agree after applying them. Consequently `hx` is
  equivalent in both directions to fixedness for the specified quotient action.
  No arbitrary action, arbitrary map, chosen representative, or extra
  hypothesis about descent is supplied.
- The first conjunct is `∃ N : ℕ, 1 ≤ N ∧ ∃ l : L, x ^ N = ...`, exactly the
  positive-integer-power conclusion. A positive integer is uniquely represented
  by a natural number at least one.
- The second conjunct is `CharZero K → ∃ l : L, x = ...`, the `N = 1` clause
  with `x ^ 1` simplified in the statement.
- The third conjunct is `∀ p : ℕ, 0 < p → CharP K p → ∃ r : ℕ, ∃ l : L,
  x ^ (p ^ r) = ...`, exactly the characteristic-`p` refinement with `r ≥ 0`.
  A field's positive characteristic is automatically prime; no extra primality
  or perfectness assumption is imposed. Neither the zero nor positive
  characteristic case is required to hold as an additional input hypothesis.

Dependency declarations read and used:

- Statement dependency `def-pc-field-extension`: `Algebra` in
  `Mathlib.Algebra.Algebra.Defs`, publicly available through the tensor imports.
- Statement dependency
  `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded
  `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `productMap`, `productMap_apply_tmul`, and `ext`
  in `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`. These give the
  standard tensor algebra, with its canonical `map` used in `hx`.
- Proof dependency
  `lem-weil-pbc-normal-extension-purely-inseparable-then-galois`:
  `Normal.fixedField_purelyInseparable_and_galois` in
  `WeilConjectures.FieldTheory.NormalExtensionFixedField` (plain proof import).
- Proof dependency `lem-weil-pbc-finite-galois-fixed-field`:
  `IsGalois.mem_range_algebraMap_iff_fixed`, `IsGalois.card_aut_eq_finrank`, and
  `AlgEquiv.fintype`, from `Mathlib.FieldTheory.Galois.Basic` and its imports.
- Proof dependency `def-weil-pbc-finite-purely-inseparable-extension`:
  `IsPurelyInseparable` and the finite-module predicate, in
  `Mathlib.FieldTheory.PurelyInseparable.Basic` and its imports.
- Proof dependency `lem-weil-pbc-finite-separable-tensor-field-reduced`:
  `Algebra.isReduced_tensorProduct_of_finiteSeparable` in
  `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`.
- Proof dependency `def-weil-ring-frobenius`: `iterateFrobeniusOfPrime` and
  `iterateFrobeniusOfPrime_apply` in
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`.
- Proof dependency `lem-weil-pbc-vector-space-basis-through-vector`:
  `Module.Basis.extend`, `Module.Basis.subset_extend`, and the basis existence
  API in `Mathlib.LinearAlgebra.Basis.VectorSpace`.
- Proof dependency `def-weil-vector-space-scalar-extension`: `TensorProduct`
  and `Module.Basis.baseChange` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, `.Tower`, and `.Basis` (with
  tensor-factor commutation for the node's convention). The statement does not
  redefine scalar extension.

All recorded proof-dependency modules are imported without `public`; the tensor
statement dependencies and other APIs needed to read the signature are public.
The declaration docstring supplies all four proof steps from the node, including
finite-group Frobenius lifting, basis coordinates, the purely inseparable fixed
field, and the final power and scalar computation.

Edge cases checked before writing:

- `x = 0` and `x = 1` satisfy the conclusions with their respective scalars and
  exponent one. There is no nonzero-element restriction.
- `E = K`, `L = K`, and degree-one extensions are included.
- For finite separable normal `E/K`, the nilradical vanishes, and fixedness
  reduces to the usual invariant tensor condition; characteristic zero requires
  precisely `x` itself to be a scalar.
- Purely inseparable finite normal extensions have trivial automorphism group:
  all reduced elements are permitted by `hx`, and the conclusion appropriately
  allows a positive characteristic power instead of incorrectly claiming that
  every invariant itself is a scalar. Mixed inseparable normal extensions are
  also included by `[Normal K E]` without `[Algebra.IsSeparable K E]`.
- Arbitrarily large or transcendental `L/K` is included: no basis index set or
  finite dimension for `L` is specified by the statement.
- The exponent `r = 0` is allowed; the general exponent `N = 0` is excluded.
  In the positive-characteristic conditional `p = 0` is excluded explicitly;
  `p = 1` cannot satisfy `CharP K p` for a field.
- The empty coordinate support in the proof uses scalar zero and auxiliary
  exponent zero. Field types exclude the zero ring, as does the node, but the
  quotient is not silently assumed to be a field or domain.

Searches for an existing statement (all run using `msearch.py`):

1. LeanFinder: `Fixed elements of the reduced tensor product of a finite normal
   field extension have characteristic powers in the base field` returned eight
   hits. The nearest were
   `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`,
   `IsPurelyInseparable.exists_pow_mem_range_tensorProduct`, Galois invariant
   results, and `IsPurelyInseparable.hasExponent_of_finiteDimensional`.
   None states the invariant result for a general normal extension after reduction.
2. Loogle: `IsPurelyInseparable, TensorProduct` returned four hits: the two
   purely inseparable tensor power results and two spectrum homeomorphism
   results. The power results assume the whole extension purely inseparable,
   so they are not this statement.
3. LeanSearch: `Invariants of reduced tensor products of normal field extensions
   are purely inseparable` returned eight hits on purely inseparable extensions,
   their characterizations, and geometric reducedness. No exact match.
4. Mathlib grep: `normal.*tensor|tensor.*invariant|exists_pow.*tensorProduct`,
   restricted to `FieldTheory`, returned the two purely inseparable tensor
   power lemmas (three source lines). No exact match.
5. Direct `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream
   declaration-name index for the item id, the chosen declaration name, and
   normal/reduced tensor invariants found no existing declaration of this
   statement. The existing
   `WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants` was read:
   it treats the unreduced tensor with a fixed-field-equals-base hypothesis,
   so it does not cover the node's inseparable normal case.
6. Direct Mathlib searches and source reads found the standard `nilradical`,
   quotient projection, normality class, and canonical tensor map APIs used in
   the signature; no new notion or dependency module is needed.

Source checked directly: `literature/stacks-project/more-algebra.tex`,
`lemma-galois-relative` (Tag 09EU). The node already corrects the source's
fixed-field shortcut for normal inseparable extensions through Fields 030M;
this delivery preserves that correction. No new statement fault or
`STATEMENT-DISPUTED` issue was found.

Validation: the prescribed `scompile.py NN
lem-sfb-normal-tensor-invariant-powers` compiled the delivered module against
both its server sandbox and library module names, cleanly (1.3 s and 1.2 s).
Only the named theorem's proof is postponed. `set_option autoImplicit false`
ensures all variables and universes are explicit.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
