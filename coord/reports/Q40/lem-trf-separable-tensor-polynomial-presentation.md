## Worker report

The module `Sheaf.FieldTheory.SeparableTensorPolynomialPresentation` states
`Algebra.exists_separable_tensor_polynomial_presentation`, with one `sorry` proof and no
new definitions. The node is unchanged except for its `lean` record. Source read:
`literature/stacks-project/algebra.tex`, Tag 0C2X,
`lemma-separable-algebraic-diagonal`, lines 10221–10259: the finite primitive-element
calculation and the union of finite subextensions. The docstring expands all five
recorded proof steps, including balancing, mapping the Bezout identity, and the zero case.

Hypotheses and clauses, in the order of the Lean signature:

- Fields and the inclusion k ⊆ L: `(k : Type u) (L : Type v) [Field k] [Field L]
  [Algebra k L]`. Field algebra maps are injective. Independent universes do not impose
  a size restriction on the extension.
- Separable algebraic extension: `[Algebra.IsSeparable k L]`. Its definition is
  separability of every minimal polynomial; `Algebra.IsSeparable.isAlgebraic` confirms
  that algebraicity is included, rather than needing an additional assumption.
- R and its arbitrary element: `(x : L ⊗[k] L)`, using the standard commutative tensor
  algebra. No finiteness assumption on L/k is made.
- The finite expansion: `∃ (n : ℕ) (a b : Fin n → L)` and
  `x = ∑ i, a i ⊗ₜ[k] b i`. Fin n merely reindexes the node's 1 through n.
- The specified generated subfield: `(E : IntermediateField k L)` and
  `E = IntermediateField.adjoin k (Set.range b)`. This is exactly k(b_1,...,b_n),
  rather than an unspecified larger field.
- Finite-dimensional and separable over k: `FiniteDimensional k E` and
  `Algebra.IsSeparable k E`, both conclusions about this same E.
- The primitive element: `(α : E)` includes membership, and
  `IntermediateField.adjoin k {(α : L)} = E` says E = k(α) inside L.
- Polynomial representatives: `(g : Fin n → Polynomial k)` and
  `∀ i, b i = Polynomial.aeval (α : L) (g i)`. The coefficient algebra map is k → L.
- P is written directly as `minpoly k (α : L)`; including α into L gives the same
  minimal polynomial as computing it in E, by injectivity of the subfield embedding.
  The bars are `Polynomial.map (algebraMap k L)`. The next two conjuncts assert
  separability of P and its image over L using `Polynomial.Separable`.
- The first displayed identity is `Polynomial.eval (α : L)
  ((minpoly k (α : L)).map (algebraMap k L)) = 0`.
- The second is `Polynomial.eval₂ ... (1 ⊗ₜ[k] (α : L)) ... = 0`, whose coefficient
  ring map is explicitly `(Algebra.TensorProduct.includeLeft :
  L →ₐ[k] L ⊗[k] L).toRingHom`. Thus t and iota are the exact canonical objects
  named in the node. The definition of eval₂ is the sum of iota(c_j) t^j.
- F is written directly as
  `∑ i, Polynomial.C (a i) * (g i).map (algebraMap k L)`. The penultimate conjunct
  evaluates it at the same t, with the same coefficient map, and gives x.
- The final conjunct evaluates this exact F at α and gives
  `Algebra.TensorProduct.productMap (AlgHom.id k L) (AlgHom.id k L) x`.
  `productMap_apply_tmul` reads a tensor as a*b, so this is exactly mu(x).
- The empty sum is permitted by `n : ℕ`, with no positivity or nonemptiness condition.
  For x=0 the witnesses n=0, E=bottom, α=0 and the empty families give P=X, F=0,
  t=0 and all four identities. Here bottom is the included copy of k. No separate
  normalization of existential witnesses is demanded by the node.

Dependency declarations used (their source signatures and docstrings were read):

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` and `IsSeparable`
  in `Mathlib.FieldTheory.Separable`, and `minpoly` in
  `Mathlib.FieldTheory.Minpoly.Basic` (publicly available through Separable).
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its universal property is `lift` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: `instCommRing`,
  `tmul_mul_tmul`, `includeLeft`, `includeRight`, `ext` in
  `Mathlib.RingTheory.TensorProduct.Basic`; `productMap` and `productMap_apply_tmul`
  in `Mathlib.RingTheory.TensorProduct.Maps`.
- `def-weil-polynomial-ring`: `Polynomial` in `Mathlib.Algebra.Polynomial.Basic`.
- `def-pc-separable-polynomial`: `Polynomial.Separable` in
  `Mathlib.FieldTheory.Separable`.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`; the statement asks for finite
  dimensionality, rendered by the standard `FiniteDimensional` predicate.
- Proof dependencies `lem-weil-pbc-algebraic-generators-finite-extension` and
  `lem-weil-pbc-simple-algebraic-extension-power-basis` are the Mathlib leaves
  `IntermediateField.finiteDimensional_adjoin` and `IntermediateField.adjoin.powerBasis`
  in `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`, publicly imported since
  the statement also uses intermediate fields and adjoin.
- Proof dependency `lem-weil-pbc-finite-separable-extension-primitive-element` is
  `Field.exists_primitive_element` in `Mathlib.FieldTheory.PrimitiveElement`,
  imported without public visibility. All proof dependencies have recorded Mathlib
  matches; no dependency module or repair is needed.

Edge cases checked before writing: x=0 and Fin 0, L=k, arbitrary finite separable
extensions, infinite separable algebraic extensions (e.g. a separable closure),
and all characteristics. For zero, minpoly(0)=X is separable even in positive
characteristic. A finite-dimensional conclusion is imposed only on E, not on L.
For nonzero x an empty expansion is impossible by the expansion equality itself.

Searches actually run using `msearch.py Q40 lem-trf-separable-tensor-polynomial-presentation`:

- `leanfinder`: "Every tensor in the tensor square of an algebraic separable field
  extension is represented by a polynomial in a primitive element of a finite
  subextension". Eight hits include `Field.primitive_element_inf_aux`,
  `Field.exists_primitive_element`, and purely inseparable tensor power results.
  None states the entire finite-support presentation and its compatible identities.
- `loogle`: `TensorProduct, minpoly`. Zero hits.
- `grep`: `tensor.*(minpoly|primitive)|exists.*(minpoly|primitive)` in `FieldTheory`.
  Twenty-one hits, including PrimitiveElement, Isaacs and Minpoly facts; no exact match.
- `leansearch`: "Finite support polynomial presentation of an element of the tensor
  square of a separable algebraic extension". Eight hits include
  `TensorProduct.exists_finsupp_left` and `exists_finsupp_right`, polynomial support,
  and multivariate polynomial tensor equivalences. They do not supply the primitive
  element and the full list of equations together.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `separable.*tensor|tensor.*polynomial|lem-trf-separable-tensor-polynomial-presentation`:
  existing reducedness, base change, and inseparability statements, no exact presentation.
- The prescribed `grep -rn` of the item id in `lean/WeilConjectures`: no hit.
- `rg -n` of the item id in `dag/lean_names_upstream.json`: no hit. Candidate declaration
  name search `separable_tensor.*presentation|separableTensor.*Presentation|separable_tensor_polynomial`
  in both Lean trees and the upstream-name index: no collision.

No statement correction, new node, dependency interface fault, or disputed statement.

## Second reading by Q40

This is a separate self-reading pass; the dispatcher brief forbids starting another
agent and reserves the independent review for the maintainer. I reread the node and
finished signature together. The generated-field equality uses precisely the right
factors, α is a member of that same field, both finiteness and separability are
conclusions, and every g_i has coefficients in k. The four equations use the mapped
minimal polynomial and the same explicit F, with the canonical left inclusion and
multiplication map. I checked that the evaluation at t has L coefficients, not k
coefficients, and that no finite-dimensional hypothesis on the infinite ambient
extension slipped in. Fin 0 and α=0 remain allowed. No mismatch was found in this pass.
