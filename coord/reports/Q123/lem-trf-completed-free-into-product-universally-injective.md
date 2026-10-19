## Worker report

The module `Sheaf.RingTheory.CompletedFreeIntoProductUniversallyInjective` constructs
`AdicCompletion.completedFreeToProduct` and states
`AdicCompletion.completedFreeToProduct_lTensor_injective`, with its sole proof `sorry`.
The source was read in `literature/stacks-project/more-algebra.tex`, Tag 05BC,
`lemma-ui-completion-direct-sum-into-product`, including the entire proof.
No statement correction, dependency repair, or new DAG node is needed.

Hypothesis and clause correspondence:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- R is Noetherian: `[IsNoetherianRing R]`, using the recorded definition.
- An arbitrary ideal I: `(I : Ideal R)`; no properness, maximality, or finite-generation
  assumption is imposed in the statement.
- R is I-adically complete, including separatedness: `[IsAdicComplete I R]`.
- An arbitrary set A: `(A : Type v)`, without finiteness or nonemptiness assumptions.
- The finitely supported free module F is `A →₀ R`, Mathlib's `Finsupp`.
- Its completion with componentwise operations is `AdicCompletion I (A →₀ R)`.
  Mathlib indexes powers by all natural numbers; the n=0 quotient is zero, so this is
  canonically the same inverse limit as the source's n>=1 indexing.
- The product is the function module `A → R`, with its ordinary pointwise operations.
- The canonical coordinate map is `completedFreeToProduct I A`. It is real data:
  `LinearMap.pi` assembles the maps
  `(ofLinearEquiv I R).symm.toLinearMap.comp
  ((AdicCompletion.map I (Finsupp.lapply a)).restrictScalars R)`.
  Completing evaluation at a gives exactly the compatible coordinate residue classes;
  the inverse of the canonical completion equivalence returns their unique limit in R.
  The helper is part of the canonical-map notion stated in this very node, and is
  recorded in `lean.declarations`, as authorized by the missing-helpers instruction.
- For every R-module Q: `(Q : Type (max u v w)) [AddCommGroup Q] [Module R Q]`.
  The maximum includes the ring and index universes and the arbitrary extra universe w;
  smaller modules can be lifted. This does not make the test-module quantifier vacuous.
- The map Q tensor iota is `(completedFreeToProduct I A).lTensor Q`, whose action is
  `q ⊗ x ↦ q ⊗ completedFreeToProduct I A x` by `LinearMap.lTensor_tmul`.
- The conclusion is exactly `Function.Injective` of this linear map.

Dependency declarations and source signatures read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg` identifying the node's finitely generated ideals.
- `Mathlib.RingTheory.AdicCompletion.Basic` (publicly imported by Functoriality):
  `IsAdicComplete`, `AdicCompletion`, `AdicCompletion.of`, and `ofLinearEquiv`.
  `ofLinearEquiv` is constructed from bijectivity of the canonical map, so its inverse
  is determined uniquely and is not an arbitrary choice of an object.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic` (through `.Map`):
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, and `TensorProduct.ext'`.
  The tensor-product dependency is a Mathlib leaf; its `mathlib_match` is used directly.
- `Mathlib.LinearAlgebra.TensorProduct.Map`: `LinearMap.lTensor` is tensoring with
  the identity on the left. The dependency records the tensor construction and the
  corresponding right tensor API; the left API has exactly the orientation this item needs.
- `Mathlib.RingTheory.AdicCompletion.Functoriality`: `AdicCompletion.map`.
- `Mathlib.LinearAlgebra.Finsupp.Defs`: `Finsupp.lapply`.
- `Mathlib.LinearAlgebra.Pi` (through the above imports): `LinearMap.pi`.
- Proof-only import `Mathlib.RingTheory.Filtration`:
  `Ideal.exists_pow_inf_eq_pow_smul`, the recorded Artin--Rees Mathlib match.
- Proof-only import `Sheaf.RingTheory.UniversalInjectiveFiniteTest`:
  `LinearMap.universally_injective_tensor_iff`; read its entire signature and proof docstring.
  Its Noetherian finite-test clause is exactly the reduction used in step 4.

The theorem docstring includes all four DAG proof steps: the convergent-family
coordinate description, a finite presentation of a finite test module, Artin--Rees
lifting of coordinate relations with orders tending to infinity, and the finite-test
criterion giving universal injectivity. No auxiliary theorem is postponed.

Edge cases checked mathematically before writing: empty A gives zero modules on both
sides; finite A gives the usual finite free completion/product identification; I=0
reduces to the ordinary free-module inclusion into the product, which splits after
restricting any tensor element to its finite coordinate support; I=R and completeness
force R to be the zero ring; the zero ring and zero Q cause no exception. Arbitrary
characteristic is allowed. The n=0 completion coordinate carries no extra restriction.

Searches for reuse (all via the required wrapper unless explicitly described as rg):

- leanfinder: "adic completion of a free module canonical coordinate map to product is
  universally injective after tensoring". Eight hits included `AdicCompletion.map_injective`,
  finite-module completion tensor results, and `ofTensorProduct_bijective_of_pi_of_fintype`;
  none states universal injectivity of the completed infinite free coordinate map.
- loogle: "AdicCompletion.map, AdicCompletion.equiv, LinearMap.pi, Finsupp.lapply".
  Zero hits, with unknown identifier `AdicCompletion.equiv`; source inspection then found
  the actual canonical inverse API `AdicCompletion.ofLinearEquiv`.
- grep: "AdicCompletion|universally.*injective" in `RingTheory/AdicCompletion`.
  Twenty-five displayed hits concern completion APIs, not the requested statement.
- leansearch: "I adic completion direct sum canonical map to product universally injective".
  Eight hits included `AdicCompletion.of_injective`, `AdicCompletion.sum`, `sum_of`,
  `map_injective`, and direct-sum inclusions. None matches the present conclusion.
- rg of `WeilConjectures/` for completion/free and coordinate/product names and the exact
  node id: no matching theorem or coordinate construction. AdicCompletion imports occur
  in unrelated padic and derived-category modules.
- rg of `lean/Sheaf` for `completed.*(Free|free)`, `completion.*(Product|product)`,
  `coordinateMap`, `intoProduct`, and the intended declaration names: only unrelated
  finite free presentations, local completion products, and geometric coordinate maps.
- rg of `dag/lean_names_upstream.json` for `completed-free-into-product`,
  `completedFreeIntoProduct`, and `completedFree.*[Cc]oordinate`: no match.

Validation: the required `scompile.py Q123
lem-trf-completed-free-into-product-universally-injective
lean/Sheaf/RingTheory/CompletedFreeIntoProductUniversallyInjective.lean` succeeded,
compiling the module alone in about 1.5 seconds with no warnings or errors.

## Second reading by Q123

This is the author's explicit self-check under the dispatcher's direct-delivery rule;
the maintainer supplies the independent review. Reopened the node and the module and
matched every binder and conclusion as listed above. In particular, the hypothesis
on completeness is on R itself, the source is the completion of finitely supported
families (not the completion of the product), the codomain is the ordinary product
of R (not a product of residue rings), and the tensor test uses Q on the left.
The coordinate map applies the inverse of the canonical completeness equivalence
rather than postulating a linear map with the desired conclusion. The helper needs
only completeness; the theorem additionally assumes exactly Noetherianity. The test
module universe covers the ring and coordinate-module universes. Empty and zero cases
remain included. No mismatch or statement dispute was found.
