## Worker report

The module `Sheaf.RingTheory.HopfAlgebra.FiniteFrobeniusForm` states
`HopfAlgebra.exists_frobenius_functional`, with its only proof `sorry`.
The node statement, statement dependencies, proof, and proof dependencies are unchanged;
only its `lean` record is supplied. No new definitions or dependency repairs are needed.

Hypotheses and clauses, matched individually:

- The field k is `(k : Type u) [Field k]`, the Mathlib leaf of `def-weil-field`.
- The unital commutative k-algebra H is `(H : Type v) [CommRing H] [HopfAlgebra k H]`.
  `HopfAlgebra` inherits `Bialgebra`, hence `Algebra k H` and the coalgebra data.
- The algebra-valued comultiplication and counit are `Bialgebra.comulAlgHom k H`
  and `Bialgebra.counitAlgHom k H`; their underlying linear maps are the coalgebra maps.
  Their algebra structures use the same `Algebra.TensorProduct` instances recorded in
  `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
- Coassociativity is the inherited `Coalgebra.coassoc`. The two tensor-unit counit
  identities are `Coalgebra.rTensor_counit_comp_comul` and
  `Coalgebra.lTensor_counit_comp_comul`.
- The antipode is `HopfAlgebra.antipode k`. The two specified antipode identities are
  exactly `HopfAlgebra.mul_antipode_rTensor_comul` and
  `HopfAlgebra.mul_antipode_lTensor_comul`. Mathlib packages the antipode initially as
  linear; in the commutative case it preserves the unit and products and yields
  `HopfAlgebra.antipodeAlgHom` (Convolution.lean:74-82). Thus the package has exactly
  the node's algebra-valued antipode, with no extra cocommutativity assumption.
- A finite basis is `(ι : Type w) [Finite ι] (basis : Module.Basis ι k H)`, using
  the basis notion carried by `def-weil-pbc-free-module`. The basis is an arbitrary
  supplied basis; its values and its index cardinality are unconstrained.
- Existence of a linear functional is `∃ φ : Module.Dual k H`. The dual is the
  existing abbreviation `H →ₗ[k] k`, with pointwise vector-space operations.
- The specified map Φ is `fun a : H => φ.comp ((LinearMap.mul k H).flip a)`.
  `LinearMap.mul k H x a` is definitionally `x * a`; `flip` fixes the second
  variable a, and composition with φ therefore evaluates at x as `φ (x * a)`.
  This gives the required product order definitionally, without using commutativity
  to disguise a different map. The codomain is precisely `Module.Dual k H`.
- The full conclusion is `Function.Bijective` of that map: both injectivity and
  surjectivity, with no omitted clause and no separate assumption of a perfect pairing.

Dependency declarations and source readings:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, class signature and docstring
  read at lines 173-186.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: Mathlib.RingTheory.TensorProduct.Basic,
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`, `includeRight`,
  `ext` (155, 311-366, 478); Mathlib.RingTheory.TensorProduct.Maps,
  `productMap`, `productMap_apply_tmul`, `productMap_left`, `productMap_right` (800-833).
  All recorded clause interfaces were read. These are imported publicly.
- `def-weil-pbc-free-module`: Mathlib.LinearAlgebra.FreeModule.Basic, `Module.Free`
  (43-44), its basis field and set-indexed equivalence (43-60), read in full.
  The item requires a finite basis rather than just freeness; it uses `Module.Basis`
  with `[Finite ι]`, as does the recorded finite-dual proof dependency.
- Mathlib.RingTheory.HopfAlgebra.Basic, `HopfAlgebraStruct` and `HopfAlgebra`
  (61-75), Mathlib.RingTheory.Bialgebra.Basic, `Bialgebra` (58-87) and its
  `counitAlgHom`/`comulAlgHom` signatures and docstrings, and the coalgebra laws
  (Coalgebra.Basic:77-86) were read to check the inline Hopf convention.
- Mathlib.LinearAlgebra.Dual.Defs, `Module.Dual` (60-63),
  Mathlib.Algebra.Algebra.Bilinear, `LinearMap.mul` (30-39), and
  Mathlib.LinearAlgebra.BilinearMap, `LinearMap.flip` (111-123), were read.

Proof-plan imports are plain imports:
`Sheaf.RingTheory.HopfAlgebra.FiniteDualHopfModule` (`finiteDualAction`,
`finiteDual_hopfModule`, full file read), `Sheaf.RingTheory.RelativeHopfModuleKernels`
(`RelativeHopf.relativeHopfModuleKernels`, including its collected conclusion), and
`Sheaf.RingTheory.CoidealCoinvariantProjection`
(`RelativeHopf.coidealCoinvariantProjection`, full current server source read with
`scompile.py --source` because the local file was absent). The Mathlib proof leaves
are imported from `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`
(`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, 197-205) and
`Mathlib.LinearAlgebra.Dual.Lemmas` (`Subspace.instModuleDualFiniteDimensional`,
`Subspace.dual_finrank_eq`, 507-517, and `LinearMap.finrank_range_dualMap_eq_finrank_range`,
920-926). Those signatures were read. `def-weil-pbc-module-tensor-product` is already
available through the public algebra-tensor import. The remaining proof dependency
`lem-sfb-relative-hopf-counit-criterion` has no recorded Lean module at this reading;
it is retained in the proof plan and DAG, with no guessed import or duplicate statement.
Its statement is not needed to type this item's statement.

The declaration docstring includes all four accepted proof steps: obtain the dual Hopf
module and specialize the relative Hopf-module criteria to k1; choose a nonzero coinvariant
and split its tensor inclusion by evaluation; deduce surjectivity of the antipode; prove
injectivity and then surjectivity of the multiplication-pairing map using equal dimensions.

Source: opened the actual Zheng PDF online at
https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Siqi.pdf,
read Theorem 4.15 and the proof of Theorem 4.8 on printed pp. 9-10. The latter uses
precisely the map sending h to evaluation of f on k*h, and proves injectivity;
equality of finite dimensions gives bijectivity. The delivered theorem is its commutative
case, as required by this DAG node. The local PDF's WANTED status is inherited and unchanged.

Edge cases checked before writing:

- H=k: the identity functional yields the usual one-dimensional product pairing.
- An empty basis would make H zero. A field-valued unital counit rules this out;
  no extra nonzero-H or nonempty-index assumption is added.
- Every characteristic is allowed. For k[t]/(t^p) with its primitive Hopf structure in
  characteristic p, the top coefficient functional pairs the monomial basis in reverse
  order nondegenerately. Thus no reducedness, separability or trace-form assumption is valid.
- For the function Hopf algebra k^G of a finite group, the sum of coordinate evaluations
  gives the diagonal perfect pairing, including when the characteristic divides |G|.
- Scalar, algebra and basis-index universes u, v, w are independent and explicitly bound.
  There is no hidden smallness condition, no automatic implicit, and no characteristic bound.

Searches actually run for this delivery:

- `msearch.py ... leanfinder`, query: “A finite dimensional commutative Hopf algebra admits
  a linear functional lambda such that a maps to the functional x maps to lambda(x*a)
  bijectively”. Eight hits: antipode identities, `HopfAlgebra.ofAlgHom`,
  `CommSemiring.toHopfAlgebra` and the antipode field. None gives the Frobenius functional.
- `msearch.py ... loogle`, query `HopfAlgebra, LinearEquiv`: zero hits.
- `msearch.py ... grep`, query `Frobenius|nondegenerate|integral`, subdirectory
  `RingTheory/HopfAlgebra`: zero hits.
- `msearch.py ... leansearch`, query: “Finite dimensional commutative Hopf algebra has
  a Frobenius functional whose multiplication pairing gives an isomorphism to its linear
  dual”. Eight hits included antipode identities and finite-dimensional dual infrastructure;
  no existence theorem for this multiplication functional.
- Direct `rg` of `lean/WeilConjectures` for HopfAlgebra/Frobenius and targeted bijective-dual
  queries: Cartier, characteristic-p Frobenius subalgebras, quotient and general-linear
  Hopf structure; the p-adic Frobenius-form basis result concerns a different extension,
  not arbitrary finite Hopf algebras. Direct node-id grep there returned no match.
- Direct `rg` of `lean/Sheaf` and its RingTheory subtree found the finite-dual Hopf-module
  construction and unrelated augmentation/Cartier statements; no copy of this theorem.

No statement dispute or source correction was found. Initial compilation rejected the
reserved token λ as an existential binder; it was renamed φ without changing the signature's
mathematical content. Final validation results are recorded below.

Validation: `scompile.py Q41 lem-sfb-finite-hopf-frobenius-form` compiled both the
sandbox probe and the intended library module successfully (3.3 s / 4.5 s), with no errors
or warnings. The signature record is verbatim, all module lines are at most 100 characters,
and the only postponed proof is the named theorem documented above.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
