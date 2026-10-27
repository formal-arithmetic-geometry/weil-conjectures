## Worker report

The module `Sheaf.RingTheory.FiniteSubcomodule` states
`Coalgebra.exists_finiteDimensional_subcomodule`, with one postponed proof and
no new definitions. It is the statement of the assigned node, without a statement
correction. Source read: Milne, Algebraic Groups (2017), Proposition 4.7, printed
p.86 (PDF p.98), and §9(d), printed pp.174–175 (PDF pp.186–187). The proof of
Proposition 4.7 uses only coassociativity and the finite basis expansion; the
counit ensures the original vectors belong to the coefficient span. This is the
general coalgebra version explicitly described in the node.

Hypotheses and clauses, matched to the Lean:

- The field is `{k : Type u} [Field k]`.
- The vector space C is `{C : Type v} [AddCommGroup C] [Module k C]`.
  `[Coalgebra k C]` supplies exactly the two linear maps and their three laws.
  In Mathlib.RingTheory.Coalgebra.Basic, `CoalgebraStruct.comul` and `.counit`
  have types `C →ₗ[k] C ⊗[k] C` and `C →ₗ[k] k`;
  `Coalgebra.coassoc` is coassociativity after `TensorProduct.assoc`, and
  `rTensor_counit_comp_comul` and `lTensor_counit_comp_comul` are the two counit
  equations before application of the canonical unit equivalences.
- The vector space M is `{M : Type w} [AddCommGroup M] [Module k M]`, with
  `(ρ : M →ₗ[k] M ⊗[k] C)`. The coaction is kept unbundled, just as in the
  existing finite-comodule coefficient-coalgebra module.
- `hcoassoc` is `(assoc k M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
  (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ ρ`.
  Thus both expressions have target `M ⊗[k] (C ⊗[k] C)` and retain right-coaction
  order. `hcounit` uses `rid k M` after `(Coalgebra.counit ...).lTensor M ∘ₗ ρ`
  and equates it with `LinearMap.id` on M.
- The arbitrary finite subset is `(T : Set M) (hT : T.Finite)`, without an
  enumeration, chosen element, or nonemptiness restriction.
- `∃ V : Submodule k M` gives an actual linear subspace of M.
  `FiniteDimensional k V ∧ T ⊆ V` is finite dimension and containment.
- `∃ ρV : V →ₗ[k] V ⊗[k] C` supplies the subspace's linear coaction.
  The next two conjuncts are precisely its coassociativity and counit identities,
  using the same ambient comultiplication and counit. They are included explicitly,
  rather than concluding only that the ambient coaction preserves V.
- The final conjunct `V.subtype.rTensor C ∘ₗ ρV = ρ ∘ₗ V.subtype` says that the
  canonical inclusion is a comodule map, exactly `(i tensor 1_C) rho_V = rho i`.
- No ring, algebra, Hopf structure, or cocommutativity on C is required.
  The three independently declared universes u, v, w allow unrelated sizes of
  the field, coalgebra, and comodule. `set_option autoImplicit false` is enabled.

Dependency declarations read and used:

- `def-weil-field` has Mathlib match `Field`, defined in
  Mathlib.Algebra.Field.Defs:180; no separate project declaration is needed.
- `def-weil-pbc-module-tensor-product` has Mathlib match `TensorProduct`, defined
  in Mathlib.LinearAlgebra.TensorProduct.Defs:81. Its tensor maps
  `LinearMap.rTensor` and `LinearMap.lTensor` are in TensorProduct.Map:331 and 326;
  `TensorProduct.assoc` and `TensorProduct.rid` are in TensorProduct.Associator:147
  and 74. These are reexported by the public Coalgebra.Basic import.
- `def-weil-finite-dimensional-subspace` has Mathlib match `FiniteDimensional`,
  the abbreviation for `Module.Finite`, in
  Mathlib.LinearAlgebra.FiniteDimensional.Defs:75, imported publicly.
- The proof dependency `lem-weil-pbc-vector-space-basis-through-vector` records
  `Module.Basis.extend`, `Module.Basis.coe_extend`, `Module.Basis.subset_extend`,
  and `linearIndepOn_singleton_iff`. Its recorded Basis.VectorSpace module is
  imported with a plain proof import. The basis-extension construction and its
  subset signature were read, including its empty independent-set case.

Edge cases checked before writing: T empty admits V = bottom with zero coaction;
M zero uses that same subspace; C zero is allowed, with the comodule counit law
forcing M zero. The canonical coalgebra k gives the usual scalar coaction and
any finite span works. No characteristic restriction occurs, and infinite-
dimensional C and M are allowed. For noncocommutative C the tensor order matches
Milne's right-comodule formula (26). No counterexample or node fault was found.

Searches actually run using the prescribed msearch.py wrapper:

- LeanFinder, `Every finite subset of a comodule over a coalgebra over a field is
  contained in a finite dimensional subcomodule`: eight hits about finite spans,
  finite sums, and finitely generated submodules, including
  `FiniteDimensional.span_of_finite`; none supplies a coaction or its stability.
- Loogle, `"Coalgebra", "FiniteDimensional"`: zero hits.
- Mathlib grep, `subcomodule|comodule.*finite|finite.*comodule`: zero hits.
- LeanSearch, `Every finite subset of a right coalgebra comodule lies in a finite
  dimensional subcomodule`: eight hits, chiefly finite-submodule tensor-product
  lemmas and finite-span dimension. These concern finitely many tensors, without
  comodule invariance, and do not state the assigned result.
- Direct rg in Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json
  for `exists_finiteDimensional_subcomodule|finite.*[Ss]ubcomodule|[Ss]ubcomodule.*finite`:
  no matches. Direct searches in the project roots for Comodule/comodule found
  coordinate Hopf coactions and the already landed
  Sheaf.RingTheory.FiniteComoduleCoefficientCoalgebra. The latter states a
  coefficient-subcoalgebra theorem for an already finite-dimensional M and does
  not produce a finite-dimensional subcomodule inside arbitrary M. Its full
  signature was read. HopfAction.Coassociative and HopfAction.Counital require
  a commutative Hopf algebra and therefore are inappropriate for arbitrary C.
- Direct rg for the node id in WeilConjectures: no match. Mathlib's
  Coalgebra.Repr.arbitrary merely presents comultiplication as a finite sum.

The declaration docstring carries all five proof steps of the node, including
coefficient extraction, coefficient stability, finite span and containment,
a linear retraction, and cancellation of the tensor inclusion to prove the
restricted coaction laws. No new notion needs an additional definition node:
the coalgebra is Mathlib's existing structure and the right-comodule laws are
written explicitly in the theorem, as they are in the node itself.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
