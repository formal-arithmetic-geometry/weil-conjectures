## Worker report

The new module `Sheaf.FieldTheory.SeparableResidueFiniteTensorFields` states
`Algebra.separableExtension_finite_tensorProduct_fields` with `sorry` as its entire proof.
It introduces no definitions. The node is unchanged except for its `lean` field; no new
nodes, dependency repairs, or statement correction are necessary. No statement dispute.

Clause-by-clause correspondence:

- The fields k, F, E are independent `Type u`, `Type v`, `Type w`, with `[Field k]`,
  `[Field F]`, `[Field E]`. `[Algebra k F]` and `[Algebra k E]` are precisely the field
  extensions of `def-pc-field-extension`, not extra embeddings or compatibility assumptions.
- Separability of F/k is `hF : Algebra.IsSeparableExtension k F`, the recorded definition
  of `def-weil-pbc-separable-field-extension`. It quantifies over every finitely generated
  intermediate field and requires it to be separably generated. It does not require F/k
  to be algebraic or finitely generated.
- Finite dimensionality of E/k is `[FiniteDimensional k E]`. There is no separability
  hypothesis on E/k.
- U is literally `F ⊗[k] E`. The standard commutative algebra tensor ring structure from
  `Mathlib.RingTheory.TensorProduct.Basic` is used. Its multiplication formula is
  `Algebra.TensorProduct.tmul_mul_tmul`; its unit formula is
  `Algebra.TensorProduct.one_def`. These are the node's prescribed operations, not extra
  conclusions or a separately defined tensor object.
- Nonzeroness is `Nontrivial (F ⊗[k] E)`.
- A nonempty finite product of fields is expressed by an existential natural number n
  with `0 < n`, a family `L : Fin n → Type (max v w)`, its field structures `hL`, and
  `Nonempty ((F ⊗[k] E) ≃+* (∀ i, L i))`. The `letI := hL` installs the existential field
  structures when forming the product; it does not introduce an additional hypothesis.
  A ring isomorphism states exactly that U is a product of fields; the node does not
  prescribe a particular decomposition or require choosing it as data. Factor fields
  can be chosen in `Type (max v w)` as quotients of U, so their universe excludes no case.
- Every prime ideal is covered by `∀ (P : Ideal (F ⊗[k] E)) [P.IsPrime]`.
- Its localization is exactly the dependency's `Localization.AtPrime P`. The existential
  `hP : IsField (Localization.AtPrime P)` states that this already specified ring is a field.
  `letI := hP.toField` equips that ring with the uniquely determined field structure so
  that the recorded general separability predicate can be applied directly to it.
- The E-algebra structure of that localization is explicitly the `RingHom.toAlgebra` of
  `(algebraMap (F ⊗[k] E) (Localization.AtPrime P)).comp
  (Algebra.TensorProduct.includeRight (R := k) (A := F) (B := E)).toRingHom`.
  `includeRight_apply` is `e ↦ 1 ⊗ e`; the localization map is `x ↦ x/1`.
  Thus the final `IsSeparableExtension E (Localization.AtPrime P)` uses exactly the map
  required by the node. No arbitrary E-action or identification with another field replaces it.

Dependency interfaces read and used:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs` (available through
  the public tensor imports); the full class and `RingHom.toAlgebra` were read.
- `def-weil-pbc-separable-field-extension`:
  `WeilConjectures.FieldTheory.SeparableExtension`, `Algebra.IsSeparableExtension` and
  `Algebra.IsSeparablyGenerated`; both full definitions and docstrings were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, used with its algebra tensor ring structure.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, read at its definition.

The module imports every stated proof dependency without `public` when it is only needed
by the proof plan: `WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced`
(`Algebra.isReduced_tensorProduct_of_isSeparablyGenerated`),
`WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable`
(`Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`),
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_free`,
`Module.Flat.lTensor_preserves_injective_linearMap`,
`Algebra.TensorProduct.includeLeft_injective`),
`Mathlib.RingTheory.Artinian.Module` (`IsArtinianRing.of_finite`,
`IsArtinianRing.equivPi`), and `Mathlib.FieldTheory.SeparablyGenerated`
(`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`). The field-extension and
localization definition modules are already public imports. All these dependency node
statements and their recorded signatures were read. The theorem docstring reproduces
all six proof steps, including tensor reassociation, the multiplicative but nonunital
coordinate inclusion, the calculation for every prime, and the characteristic split.

Source verification: read the local `literature/stacks-project/algebra.tex` at
`lemma-characterize-separable-field-extensions` (Tag 030W),
`lemma-geometrically-reduced-permanence` (Tag 04KN),
`lemma-finite-dimensional-algebra` (Tag 00J6), and `lemma-product-local` (Tag 00JA).
030W assumes positive characteristic, which is why the proof docstring keeps the
separate characteristic-zero argument. No such characteristic restriction is added to
this theorem.

Edge cases checked mathematically before writing:

- E=k gives U=F; the single prime localization is F with its original k-action.
- F=k allows an arbitrary finite, including purely inseparable, E/k; U=E and its
  extension over E is the identity and hence separable.
- For k=F_p(s), F=k(t), E=k(s^(1/p)), the tensor is E(t). Thus transcendental F and
  inseparable finite E must both remain permitted, as they do here.
- Finite separable E/k split by F can produce several field factors; the conclusion
  does not assert that U itself is a field.
- The empty product/zero ring is excluded by nonzeroness and `0 < n`, consistent with
  both inputs being fields. Different universes for the three fields remain allowed.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder` with query "A separable possibly transcendental field
  extension tensored with a finite field extension is a nonzero finite product of fields,
  and each prime localization is separable over the finite extension": eight hits.
  `Algebra.TensorProduct.isField_of_isAlgebraic` assumes the tensor is a domain;
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod` concerns finite type algebraic
  separability. The other linear-disjointness and reducedness hits do not state this node.
- `msearch.py ... loogle 'Algebra.IsSeparableExtension, TensorProduct, Localization.AtPrime'`:
  zero hits, unknown identifier `Algebra.IsSeparableExtension` (the predicate is a project
  declaration, not in the Mathlib search index).
- `msearch.py ... grep 'isSeparable.*[Tt]ensor|[Tt]ensor.*isSeparable|[Ss]eparable.*[Ll]ocalization'
  FieldTheory`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the node id and separable/tensor
  and separable/localization patterns found related general geometric-normality results,
  finite separable/algebraically closed decompositions, and the special algebraic
  separable/purely inseparable tensor result. None states both of this node's conclusions
  for arbitrary separable F/k and arbitrary finite E/k. The exact node id has no existing
  module. `dag/lean_names_upstream.json` similarly records the reducedness criterion and
  the special purely inseparable scalar-descent result, not this statement. The new full
  declaration name was searched in both project roots and Mathlib with no collision.

Validation: the prescribed `scompile.py` compiled both its sandbox and final module
probes cleanly (1.6 s and 1.5 s respectively); no errors or unexpected warnings.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
