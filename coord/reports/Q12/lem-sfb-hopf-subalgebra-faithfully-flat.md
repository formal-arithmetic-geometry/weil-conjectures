## Worker report

The delivery states `HopfAlgebra.faithfullyFlat_of_injective` in
`Sheaf.RingTheory.HopfAlgebra.SubalgebraFaithfullyFlat`. Its sole proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement changes.
The original node is copied with only its `lean` field added.

Source checked: Milne, Algebraic Groups (2017), Definition 3.3 and the observations
3.4, printed pp. 65--66; Definition 3.8, p. 67; Theorem 3.31 and its proof,
pp. 73--74. These were read from the supplied PDF using pdftotext. Theorem 3.31
asserts faithful flatness for finitely generated commutative Hopf inclusions over
an arbitrary field. The accepted DAG proof avoids the invalid A-linear splitting
sentence in the source's nilpotent special-case argument. This delivery retains
the DAG's named basis-lifting input instead of using that sentence.

Clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`.
- The unital commutative algebras A and B are `(A : Type v) (B : Type w)` with
  `[CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]`.
  The Hopf classes extend `Bialgebra`, hence supply their k-algebra structures.
- The comultiplications and counits are `Bialgebra.comulAlgHom k A` and
  `Bialgebra.counitAlgHom k A`, and the corresponding maps for B. The inherited
  `Coalgebra` gives coassociativity and both counit identities with the canonical
  tensor associator and unit maps. `Bialgebra` gives multiplicativity and units.
- The antipodes are `HopfAlgebra.antipode k`; for commutative A or B these are
  the underlying linear maps of Mathlib's `HopfAlgebra.antipodeAlgHom`.
  The two `HopfAlgebra.mul_antipode_*Tensor_comul` fields express precisely
  multiplication after S tensor identity and identity tensor S being unit after
  counit. Thus Mathlib's linear-map presentation of the antipode imposes exactly
  the node's algebra-map condition in this commutative setting.
- Both finite-generation hypotheses use the dependency's recorded declaration
  `RingHom.FiniteType`: `hA : (algebraMap k A).FiniteType` and the same for B.
- The k-algebra homomorphism is the underlying algebra map of `i : A →ₐc[k] B`.
  `BialgHom` includes the exact compatibility identities for comultiplication
  and counit (see `BialgHomClass.map_comp_comulAlgHom` and
  `BialgHomClass.counitAlgHom_comp`). Injectivity is `hi : Function.Injective i`.
- The third compatibility identity is written explicitly as
  `hS : ∀ a : A, antipode k (i a) = i (antipode k a)`.
- The conclusion is the recorded `Module.FaithfullyFlat A B`, with its module
  argument explicitly fixed to `i.toAlgHom.toRingHom.toAlgebra.toModule`.
  This avoids both an unrelated A-action and an extra choice of algebra structure.
  Mathlib's `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` identifies this
  class with the node's preservation and reflection of exactness of complexes.
- There is no reducedness, perfectness, smoothness, cocommutativity, characteristic,
  connectedness, or algebraic-closure binder. The universes u,v,w are independent.

Dependency declarations and imports, signatures and docstrings read:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`.
- lem-weil-pbc-algebra-tensor-pushout-universal-property:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `ext` in `Mathlib.RingTheory.TensorProduct.Basic`, and
  `productMap`, `productMap_apply_tmul`, `productMap_left`, `productMap_right`
  in `Mathlib.RingTheory.TensorProduct.Maps`. These are the tensor products
  inherited by the Hopf and bialgebra structures; Maps is publicly imported.
- def-weil-pbc-finite-type-algebra: `RingHom.FiniteType` in
  `Mathlib.RingTheory.FiniteType` (and its `finiteType_algebraMap` equivalence).
- def-weil-pbc-faithfully-flat-ring-map: `Module.FaithfullyFlat` and
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
- Existing Mathlib notions `HopfAlgebra`, `HopfAlgebra.antipodeAlgHom`,
  `BialgHom` and its algebra/coalgebra compatibility fields are reused directly.
- Proof-only import: `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` for
  def-weil-algebraic-closure, and
  `Sheaf.RingTheory.HopfAlgebra.ReducedCoreNilpotentFibre` for the recorded
  `HopfAlgebra.exists_reduced_core_nilpotent_fibre`.
- The flat-injection, faithful-flat-reflection and faithful-flat-base-change
  Mathlib proof inputs are available through `Flat.FaithfullyFlat.Basic`:
  `Module.Flat.lTensor_preserves_injective_linearMap`,
  `Module.FaithfullyFlat.lTensor_injective_iff_injective`, and
  `Module.FaithfullyFlat.instTensorProduct`. The field-extension base-change
  input uses that same instance and vector-space freeness.
- The other three substantive proof nodes (reduced target, relative kernel shear,
  nilpotent basis lifting) have no Lean record in the read clone. They are named
  in the six-step docstring; there is no declared module to import for them.

Edge cases checked before writing:

- A = B with identity map gives the faithfully flat regular module.
- A = k includes the empty algebra-generating family; the counit makes B nonzero,
  so its vector-space module is nonempty free and faithfully flat.
- A zero algebra cannot carry this counit over a nonzero field, since it preserves
  both zero and one. No explicit Nontrivial assumption is necessary or added.
- Infinitesimal examples such as k[t]/(t^p) in characteristic p are allowed;
  the signature contains no `IsReduced` or characteristic-zero restriction.
  Frobenius inclusions k[t] → k[x], t ↦ x^p, are included as Hopf maps.
- Noncocommutative coordinate Hopf algebras are allowed: `HopfAlgebra` has no
  cocommutativity field. Imperfect base fields are likewise not excluded.
- Independent universes for the field and the two algebras do not impose any
  equality or a universe-limited test-object quantifier.

Searches (2026-10-24, through the prescribed msearch.py wrapper):

- LeanFinder: "An injective morphism of finitely generated commutative Hopf
  algebras over a field is faithfully flat". Eight hits, all general faithful-flat
  definitions, consequences, or descent; none derives flatness from Hopf inclusion.
- LeanSearch: "An injective homomorphism of finite type commutative Hopf algebras
  over a field is faithfully flat". Eight hits, the same generic flatness and
  faithful-flatness API; no Hopf inclusion theorem.
- Loogle: `"HopfAlgebra", "FaithfullyFlat"`. Zero hits.
- Mathlib grep: `Hopf.*[Ff]lat|[Ff]lat.*Hopf`. Zero hits.
- Project rg with that regex and the node id across lean/WeilConjectures and
  lean/Sheaf found only the existing downstream proof-plan citation and the
  unrelated field-extension assertion in AugmentationHeight. No declaration
  states this theorem. The exact required upstream node-id grep has no hits.
- Exact-name rg `faithfullyFlat_of_injective` in Mathlib, both project roots and
  dag/lean_names_upstream.json has no hits. Read the Mathlib Hopf/Bialgebra APIs
  and the existing reduced-core module rather than introducing duplicate notions.

Validation: scompile.py compiled this file both as a sandbox module and under its
intended library module name, with no errors or warnings reported (3.5 s and 2.6 s).
The module has one named theorem, one whole-proof sorry, explicit type/universe
binders, no file-local instances/notation, and no line exceeding 100 characters.

## Second reading by Q12

Reopened the node and the completed Lean file in a separate reading pass. Checked
Field and both CommRing/HopfAlgebra binders, both finite-type hypotheses, the
bialgebra morphism's counit and comultiplication fields, explicit antipode equality,
injectivity, and the exact induced module argument of the conclusion against the
corresponding prose clauses. All match. In particular the HopfAlgebra linear
antipode is an algebra map by the imported commutative antipodeAlgHom API, not an
extra assumption; no cocommutativity is hidden in the inherited coalgebra axioms.
The proof docstring follows all six DAG steps and retains their descent maps.
No signature mismatch or statement change was found. This is the worker's own
second pass; no independent agent was started, as required by the dispatcher.
The maintainer's independent review remains the independent reading.
