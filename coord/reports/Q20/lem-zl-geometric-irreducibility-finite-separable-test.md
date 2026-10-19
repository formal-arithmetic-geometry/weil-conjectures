# Q20: finite separable tests for geometric irreducibility

## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest` states
`Algebra.irreducibleSpace_tensorProduct_iff_finite_separable`, with one `sorry` and no
new definitions. The node is unchanged except for its `lean` record. I read Stacks
Algebra, Tag 037K (`lemma-geometrically-irreducible`), all four conditions and the
proof. The present theorem is precisely equivalence (1) and (2).

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| An arbitrary commutative k-algebra R, including the zero ring | `(R : Type v) [CommRing R] [Algebra k R]`; the homomorphism is `algebraMap k R` |
| Tensor product of the underlying k-modules | `R ⊗[k] L` and `R ⊗[k] E`, Mathlib's `TensorProduct` |
| Multiplication `(r ⊗ a)(s ⊗ b) = rs ⊗ ab` and unit `1 ⊗ 1` | The canonical `Algebra.TensorProduct.instCommRing`, with `tmul_mul_tmul` and `one_def` from `Mathlib.RingTheory.TensorProduct.Basic` |
| Clause (1): every field extension L/k | `∀ (L : Type (max u v w)) [Field L] [Algebra k L], ...` |
| Clause (2): every finite separable algebraic extension E/k | `∀ (E : Type (max u v w)) [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E], ...` |
| Finite means finite-dimensional as a k-vector space | `FiniteDimensional k E`, definitionally `Module.Finite k E`, rather than an inequality involving the zero-on-infinite convention for `finrank` |
| Algebraic and separable | `Algebra.IsSeparable k E` means every minimal polynomial is separable and already implies algebraicity (`Algebra.IsSeparable.isAlgebraic`) |
| The affine spectrum of each tensor-product ring | `AlgebraicGeometry.Spec (CommRingCat.of (R ⊗[k] L))`, respectively E |
| Irreducible, including nonempty | `IrreducibleSpace (...)`, which extends `PreirreducibleSpace` with `toNonempty` |
| Equivalence of (1) and (2) | `↔`, with the all-extension clause on the left |
| No finite-generation or reducedness hypothesis on R | No `FiniteType`, `Module.Finite`, `IsReduced` or `Nontrivial` binder on R |

All universes are explicitly declared (`universe u v w`) and auto-implicits are disabled.
Both test-field universes are `max u v w`, hence cannot lie below k or R. The free w
allows arbitrarily large test fields; smaller extensions can be lifted to this common
universe without changing their tensor-product spectra. The test at the identity
extension is retained, using an isomorphic universe lift when necessary.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`; field
  extensions are `[Field L] [Algebra k L]`. No custom extension structure is introduced.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`; its docstring and algebraicity instance were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, reexported by the tensor-product ring
  module. The same module tensor product receives its canonical ring structure.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`; the statement uses this actual scheme.
- `def-weil-irreducible-components`: `irreducibleComponents` and `IsIrreducible` in
  `Mathlib.Topology.Irreducible`; the whole-space version is `IrreducibleSpace` from
  that same module, with the required nonempty convention.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`. Finiteness itself is correctly expressed
  by `FiniteDimensional`, from `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, whose
  signature and docstring were read. No new dimension function is defined.

The six-step proof docstring follows the node, including tensor reassociation and
faithful-flat injectivity, nonemptiness at E = k, descent of finitely many coefficients
and their nilpotence equation to one finite separable extension, the common overfield
and separably closed tensor theorem, and contraction of the prime nilradical.
Available proof dependencies are imported without `public`: tensor-product maps,
faithfully-flat ideal contraction (also importing the faithfully-flat base-change
instances), the prime-spectrum nilradical criterion,
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed` for
`IsSepClosure.exists_intermediateField_mem`, and
`Sheaf.FieldTheory.CommonExtensionFields` for `Field.exists_common_extension`.
The node `lem-zl-sepclosed-algebras-tensor-irreducible` presently has no recorded
statement module, so no import can yet be added for it. It is needed only for the
future proof, not to type this statement, and is named explicitly in step 5.

Edge cases checked before writing:

- R = 0: tensor products are zero rings and their spectra are empty. Both conditions
  are false, including the right side because the degree-one test is included.
- R = k: every tensor product is the test field, with a one-point spectrum, so both
  conditions hold.
- R = k × k: the identity extension already yields a reducible spectrum, so both
  conditions fail.
- R = k[epsilon]/(epsilon^2): spectra remain irreducible under field extensions;
  nilpotents are allowed and no domain or reducedness conclusion was substituted.
- R a separable quadratic field over k: its tensor product with that finite separable
  splitting field is reducible, so the right side detects failure of geometric
  irreducibility. Purely inseparable extensions in positive characteristic remain
  permitted among L; no perfectness or characteristic restriction is imposed.
- Infinite-dimensional algebras such as polynomial rings in infinitely many variables
  are admitted. Finite-dimensionality restricts E/k only, not R/k.

Searches (all remote searches used `msearch.py`, recorded in `searches.jsonl`):

- LeanFinder query: "An algebra over a field has irreducible spectrum after every
  field extension if and only if it does after every finite separable field extension".
  Eight hits, principally `Algebra.IsGeometricallyReduced`, its algebraic-closure test,
  etale decomposition and `Algebra.IsSeparable`. None gives this irreducibility test.
- LeanSearch query: "Geometric irreducibility of the spectrum of an algebra is
  equivalent to irreducibility after every finite separable extension of the base
  field". Eight hits, including domain-spectrum irreducibility, purely inseparable
  spectral homeomorphisms, geometrically reduced algebras and separable closures.
  None states the equivalence for arbitrary commutative algebras.
- Loogle query: `AlgebraicGeometry.GeometricallyIrreducible, Algebra.IsSeparable,
  IrreducibleSpace`. Zero hits for this combined query; this is not taken as absence
  of the individual definitions, which were read in source.
- Mathlib grep query: `geometrically.?irreducible|finite.*separable|separable.*finite`
  in `AlgebraicGeometry/Geometrically`. Eleven hits. I read
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible` in full: it defines the scheme
  property and proves stability, composition and fibre criteria, but has no finite
  separable test. The geometrically reduced results concern a different property.
- Source `WeilConjectures/` grep: the item id has no occurrence. Searches for
  geometric irreducibility, finite separable irreducibility and Tag 037K found the
  surjective-image theorem, smooth connected-fibre irreducibility, Bertini/generic
  irreducibility results and irreducible Weil sheaves, not this algebra theorem.
  I read the entire upstream `Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean`.
- Project `lean/Sheaf/` grep: no item id or finite-separable irreducibility test.
  The finite-separable *connectedness* theorem concerns a different property and
  is not an existing declaration for this node.
- Exact new declaration and module names were searched in Mathlib, upstream and
  the project: no collision.

No statement correction, dependency repair, new node or mathematical dispute is needed.
The previous worker's rejection concerned the stage-1 split already reviewed by Q76;
that stage-1 result has no `lean` record. This delivery supplies the separate stage-2
statement and preserves the accepted split.

Validation: `scompile.py Q20 lem-zl-geometric-irreducibility-finite-separable-test`
compiled the single module cleanly in both sandbox and library modes (16.8 s and
5.1 s respectively). The JSON differs from the supplied node only in `lean`; its
signature is copied verbatim from the file. Every Lean line is at most 100 characters.
The required delivery dry run and final push are performed after this report is written.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
