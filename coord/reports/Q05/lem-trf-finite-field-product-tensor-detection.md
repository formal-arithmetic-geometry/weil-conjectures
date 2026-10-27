## Worker report

The module `Sheaf.RingTheory.FiniteFieldProductTensorDetection` states
`Algebra.finite_field_product_tensor_detection`. Its only theorem proof is `sorry`.
No definitions or additional nodes are needed. No node field other than `lean` changes.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`.
- The commutative k-algebras A and B are independent types in universes v and w,
  each with `[CommRing ...] [Algebra k ...]`. There is no Nontrivial, finite-type,
  finite-dimensional, or reducedness hypothesis on either algebra.
- The finite set is `(I : Type t) [Finite I]`. This requires neither Nonempty I
  nor a choice of enumeration or decidable equality.
- The family of extension fields is `(K : I → Type s) [∀ i, Field (K i)]
  [∀ i, Algebra k (K i)]`, using the recorded field-extension encoding.
- P is Mathlib's dependent product `∀ i, K i`, with its existing coordinatewise
  commutative-ring and k-algebra structures. The map and injection are
  `(j : B →ₐ[k] (∀ i, K i)) (hj : Function.Injective j)`; AlgHom preserves 1.
- Tensor products are Mathlib `TensorProduct`, written `⊗[k]`, with the existing
  algebra tensor-product ring structure. Its multiplication and unit are exactly
  `Algebra.TensorProduct.tmul_mul_tmul` and `Algebra.TensorProduct.one_def`.
- The first conclusion gives an algebra equivalence
  `Φ : ((∀ i, K i) ⊗[k] A) ≃ₐ[k] (∀ i, K i ⊗[k] A)` together with
  `∀ x a i, Φ (x ⊗ₜ[k] a) i = x i ⊗ₜ[k] a`. This specifies the canonical map
  on all pure tensors, hence uniquely on the tensor product; an AlgEquiv is a
  unital k-algebra isomorphism. The characterization prevents an arbitrary
  unspecified equivalence from satisfying the conclusion.
- The second conclusion is injectivity of the actual canonical AlgHom
  `AlgHom.pi (fun i ↦ Algebra.TensorProduct.map
  ((Pi.evalAlgHom k K i).comp j) (AlgHom.id k A))`.
  By `AlgHom.pi_apply`, `Algebra.TensorProduct.map_tmul`, the evaluation map,
  and the identity map, it sends `b ⊗ₜ a` to the family `j b i ⊗ₜ a`.
- The final conclusion is exactly
  `(∀ i : I, IsReduced (A ⊗[k] K i)) → IsReduced (B ⊗[k] A)`.
  In particular, the hypothesis keeps the node's A-first tensor orientation.
  Mathlib IsReduced means that every nilpotent element equals zero.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with
  Field on both k and K i, exactly as that node's existing record directs.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.mk`,
  `TensorProduct.lift` and `TensorProduct.ext'` give pure-tensor generation and
  its universal property. These are publicly available through the algebra
  tensor-product import. No replacement tensor notion is defined.
- Proof dependency `lem-weil-pbc-tensor-finite-product`: `TensorProduct.piLeft`,
  `Mathlib.LinearAlgebra.TensorProduct.Pi`, imported through the public Pi module.
- Proof dependency `lem-weil-pbc-module-tensor-comm`: `TensorProduct.comm`,
  `TensorProduct.comm_tmul`, `TensorProduct.map_comp_comm_eq`, in Basic/Map,
  available through the public Pi module. `Algebra.TensorProduct.comm` is its
  existing multiplicative refinement in `Mathlib.RingTheory.TensorProduct.Maps`.
- Proof dependency `lem-weil-pbc-flat-tensor-exact`: `Module.Flat.rTensor_exact`
  and `Module.Flat.lTensor_exact`, `Mathlib.RingTheory.Flat.Basic` (plain import).
- Proof dependency `lem-weil-pbc-module-over-field-flat`: `Module.Flat.of_free`
  from Flat.Basic and `Module.Free.of_divisionRing` from
  `Mathlib.LinearAlgebra.Basis.VectorSpace` (plain import).

Source read: `literature/stacks-project/algebra.tex`, lines 10129–10151,
`lemma-geometrically-reduced-any-reduced-base-change`, Tag 034N. Its final
reduction through an embedding in a finite product of fields is exactly the
argument expanded by this node. The complete four-step DAG proof is rendered
in the theorem docstring: finite-product linear equivalence, multiplicative
upgrade, field flatness preserving j's injectivity, and nilpotent detection
using tensor symmetry. Module quotient P/j(B) is explicitly a module quotient.

Edge cases checked before drafting: empty I gives a singleton product ring;
injectivity of j then forces B to be the zero ring, so both injection and
reducedness conclusions still hold. A=0 and B=0 are permitted, with zero tensor
products wherever applicable. For singleton I, the product comparison reduces
to the ordinary tensor of j. A diagonal embedding k into k×k gives the expected
diagonal tensor map. No characteristic or separability restriction is imposed.
The five universes u,v,w,t,s are explicitly bound and independent; no equality
between the coefficient, algebra, index, or extension universes is assumed.

Searches actually run using the prescribed msearch wrapper:

- leanfinder: "An injective algebra homomorphism into a finite product of fields
  remains injective after tensoring over a field and detects reducedness".
  Eight hits, including `Algebra.IsGeometricallyReduced.of_injective`,
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`,
  and `IsReduced.tensorProduct_of_flat_of_forall_fg`; none states this item.
- loogle: `TensorProduct, IsReduced`. Six hits concerning geometric reducedness,
  algebraic extensions, or the finite-generation reduction criterion; no match.
- grep: `IsReduced.*tensor|tensor.*[Ii]sReduced|piRight`, subdirectory RingTheory.
  Fourteen hits; read GeometricallyReduced.lean, Flat.Basic's finite-generation
  criterion, and TensorProduct.Pi.lean. Algebra.TensorProduct.piRight supplies
  an existing product equivalence (in the swapped orientation), but not the
  combined injection and reducedness statement.
- leansearch: "Tensoring an injection into a finite product of field extensions
  detects reducedness". Eight hits, again geometric reducedness and injectivity
  lemmas, with no whole-item match.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `finite.field.product|finiteFieldProduct|tensor.*[Dd]etect|product.*tensor.*reduced`:
  no matching statement. Direct item-id search in WeilConjectures found none.
- Full-name search `finite_field_product_tensor_detection|finiteFieldProductTensorDetection`
  in both source trees and dag/lean_names_upstream.json found no collision.

There is no STATEMENT-DISPUTED issue and no statement correction.

Validation: scompile.py checked the delivered module against current server
sources successfully. The local compiler path reported ENOSPC, and the wrapper
completed its prescribed server confirmation with exit 0; the server file check
took 1.1 seconds. No live file or tool was edited to obtain that result.

## Second reading by Q05

A second sequential reading by the same worker checked the full node against
this file; the maintainer supplies the independent review after delivery.
The equivalence's pure-tensor equation fixes the same canonical Phi, and the
AlgHom.pi expression fixes Theta with the required j-coordinate formula.
The reducedness premise is A tensor K_i, while the detected ring is B tensor A.
The finite binder excludes neither the empty family nor large finite types,
and the algebra binders impose no nonzero or finite-generation hypothesis.
All proof dependencies have imports, all variables and universes are bound,
and the theorem contains the sole sorry. No mismatch was found in this pass.
