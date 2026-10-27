## Worker report

The module `Sheaf.RingTheory.CoalgebraDualActionDetection` supplies the actual
canonical operator `Coalgebra.dualContraction` and the statement
`Coalgebra.dual_action_detection`. Its one theorem has proof `sorry`.
The helper belongs to the action described by this item; it is the composite
of existing tensor maps, without any chosen or postponed data. No new notion,
dependency repair, or statement correction is needed.

Hypotheses and clauses, matched against the node:

- The field is `{k : Type u} [Field k]`. The vector space C is
  `{C : Type v} [AddCommGroup C] [Module k C]`. `[Coalgebra k C]`
  packages exactly Delta, epsilon, coassociativity and both counit identities.
  Mathlib's `Coalgebra` definition was read in `Coalgebra/Basic.lean`.
- The dual algebra A is `WithConv (C →ₗ[k] k)`, using the recorded convolution
  dependency's `LinearMap.convRing` and `LinearMap.convAlgebra`. `WithConv`
  changes the multiplicative instance, retaining the underlying linear maps,
  addition and scalar multiplication. Its unit and scalar map are exactly
  epsilon and a epsilon by `convOne_apply` and `convAlgebraMap_apply`.
- M has independent universe w and the vector space instances. Its coaction
  is `ρM : M →ₗ[k] M ⊗[k] C`. `hcoassocM` is the stated coassociativity
  with `TensorProduct.assoc`, `rTensor`, and `lTensor`; `hcounitM` is the
  stated right counit equation with the canonical `TensorProduct.rid`.
- T_f is exactly `dualContraction ρM f`, defined as
  `(TensorProduct.rid k M).toLinearMap ∘ₗ f.lTensor M ∘ₗ ρM`.
  The first conjunct asserts an algebra homomorphism T with these exact
  values on every f; it therefore includes additivity, k-linearity, the
  multiplication law and preservation of the unit. The next two conjuncts
  spell out the node's particular equations for f*g (in the given order)
  and a epsilon. No opposite algebra or reversed composition is used.
- An arbitrary subspace is `W : Submodule k M` with inclusion `W.subtype`.
  The stability condition quantifies over all `f : C →ₗ[k] k` and all
  `m ∈ W`. Its equivalent condition is `∃! ρW`, satisfying exactly
  `W.subtype.rTensor C ∘ₗ ρW = ρM ∘ₗ W.subtype`.
  Thus existence and uniqueness are among ALL linear maps with the equation,
  rather than only among maps already assumed to satisfy the comodule laws.
- The next conjunct quantifies over W and any such ρW and proves that
  factorization implies BOTH coassociativity (with `assoc`) and the counit
  law (with `rid`). In combination with the preceding conjunct this is
  precisely the unique restricted coaction and its automatic identities.
- For the last clause N is an arbitrary vector space in independent universe z,
  with an arbitrary linear coaction ρN and both comodule identities as
  hypotheses. For every `u : M →ₗ[k] N`, the tensor comodule-map equation
  is equivalent to `u ∘ₗ dualContraction ρM f = dualContraction ρN f ∘ₗ u`
  for EVERY functional f.
- There is no `FiniteDimensional`, `IsCocomm`, `Nontrivial C`, or
  `Nontrivial M` binder. The dual is the full algebraic dual.

Dependency declarations used:

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`), exposed
  through the public convolution import.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `TensorProduct.lift`, `TensorProduct.ext'`, `LinearMap.lTensor`,
  `LinearMap.rTensor`, `TensorProduct.assoc`, and `TensorProduct.rid`,
  exposed by `Mathlib.RingTheory.Coalgebra.Convolution`. Their definitions
  and relevant signatures were read in Defs, Basic, Map and Associator.
- `lem-sfb-convolution-linear-map-algebra`: `LinearMap.convRing`,
  `LinearMap.convAlgebra`, `convMul_apply`, `convOne_apply`, and
  `convAlgebraMap_apply` from `Mathlib.RingTheory.Coalgebra.Convolution`.
- Proof import `Mathlib.LinearAlgebra.Dual.Lemmas` supplies
  `Module.Projective.exists_dual_ne_zero`, the recorded match of
  `lem-weil-pbc-vector-space-dual-separates`.
- Proof import `Mathlib.LinearAlgebra.Basis.VectorSpace` supplies
  `Submodule.exists_isCompl`, the recorded match of
  `lem-trf-vector-subspace-complement`, as well as freeness over a field.
- Proof import `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis`
  supplies `TensorProduct.eq_zero_of_forall_rTensor_eq_zero`, read in full,
  the recorded upstream declaration of
  `lem-sfb-vector-space-tensor-family-zero-detection`.

The theorem's docstring carries all six DAG proof steps: the action laws,
zero detection by the full dual, complements and tensor injectivity,
factorization and uniqueness, descent of both coaction identities, and
zero detection of the defect of an intertwiner.

Edge cases checked before writing: C=0 is a valid coalgebra; the counit
law then forces every comodule M to be zero. The dual convolution ring is
then the zero ring, and the asserted unital map into End(0) is valid.
M=0, N=0, W=0 and W=M all give the appropriate unique zero maps or the
original coaction. For C=k with its standard coalgebra, T_f is scalar
multiplication and all subspaces are stable, as required. Infinite-dimensional
spaces cause no change: each tensor is a finite sum, all functionals occur,
and no finite-dimensional duality or tensor-dual surjectivity is assumed.
The order T_(f*g)=T_f composed with T_g was checked directly on the two
coassociativity expansions; no cocommutativity is needed.

Searches made (2026-10-24):

- `msearch.py ... leansearch "A right coalgebra comodule has a convolution
  dual algebra representation detecting invariant subspaces and comodule maps"`:
  eight results, including convolution structures and `Coalgebra.Repr`;
  no action or detection theorem.
- `msearch.py ... leanfinder "Right comodules over a coalgebra have a
  convolution dual algebra action detecting subcomodules and comodule morphisms"`:
  eight results, primarily `CoalgCat` comonoid equivalences and the convolution
  commutative ring; none states this theorem.
- `msearch.py ... loogle "LinearMap.convAlgebra, Coalgebra"`: twelve
  results, including the exact convolution algebra API and pre/postcomposition;
  no comodule action or detection assertion.
- `msearch.py ... grep "Comodule|comodule|dualAction|dual_action"
  RingTheory/Coalgebra`: zero results.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for comodule names
  found finite-subcomodule and finite-coefficient statements with explicit
  coaction equations, and the affine Hopf coaction predicates. These neither
  construct the general dual action nor state its detection properties.
  The affine Hopf predicates require a commutative Hopf algebra and so are
  unsuitable for a general coalgebra. The present theorem uses the explicit
  tensor equations already used in the general finite-subcomodule interface.
- `rg` for the item id in `lean/WeilConjectures` found no match.
- `rg` over Mathlib, both project roots and `dag/lean_names_upstream.json`
  for `dualContraction|coalgebra_dual_action_detection` found no match.

Source checked directly: Milne's local PDF, printed pp.174–175 (PDF pages
186–187), defines coalgebras, the convolution dual and right comodules.
Example 9.36, printed p.178 (PDF page 190), gives the finite algebra special
case. The node explicitly supplies the general contraction-detection proof;
the delivery preserves that generality. No statement dispute or node fault
was found.

Validation: the module is compiled using the prescribed server wrapper;
`deliver2.py --no-push` checks the complete packet before delivery.

The initial compile exposed namespace shadowing by `Coalgebra.TensorProduct`
from the convolution imports. All vector-space associators and right unit
equivalences now use `_root_.TensorProduct` explicitly; this changes no
mathematical statement.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
