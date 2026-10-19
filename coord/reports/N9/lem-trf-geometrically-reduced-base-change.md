## Worker report

The module `Sheaf.RingTheory.GeometricallyReducedBaseChange` states
`isReduced_tensorProduct_of_forall_fieldExtension`, with the single proof `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The repository and upstream checkout were read only; all authored files are in the
assigned sandbox. Compilation and delivery use the prescribed wrappers exclusively.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The field `k` is `(k : Type u) [Field k]`.
- The commutative `k`-algebra `A` is `(A : Type v) [CommRing A] [Algebra k A]`.
- Remaining reduced over every extension field is the explicit hypothesis
  `hgeom : ∀ (L : Type (max u v w)) [Field L] [Algebra k L], IsReduced (A ⊗[k] L)`.
  The quantifier includes every field structure and every `k`-algebra structure on
  each test carrier; a unital map from a field to a field is injective. This does
  not substitute the algebraic-closure-only definition of
  `Algebra.IsGeometricallyReduced` for the stated hypothesis.
- The arbitrary reduced commutative `k`-algebra `R` is
  `(R : Type w) [CommRing R] [Algebra k R] [IsReduced R]`.
- The conclusion is exactly `IsReduced (R ⊗[k] A)`, with factors in the node's order.
- Reduced means no nonzero nilpotents: the Mathlib class `IsReduced` has field
  `eq_zero : ∀ x, IsNilpotent x → x = 0` (Algebra/GroupWithZero/Basic.lean:191).
- The tensor product is the dependency's actual `TensorProduct k R A`, with its
  canonical commutative algebra ring structure supplied by
  `Mathlib.RingTheory.TensorProduct.Basic`. In particular
  `Algebra.TensorProduct.tmul_mul_tmul` gives the stated multiplication and
  `Algebra.TensorProduct.one_def` gives the stated unit. These are the selected
  structure's laws, not additional hypotheses or new conclusion conjuncts.
- There is no `FiniteType`, `FiniteDimensional`, `Nontrivial A`, `Nontrivial R`,
  perfectness, characteristic, or domain hypothesis.

Universes are explicitly bound as `u v w` with independent carriers for `k`, `A`,
and `R`. The test-field universe `max u v w` contains all three universes. It is
not an unrelated smaller universe, which could make the hypothesis vacuous.
All minimal-prime residue fields of a finitely generated `k`-subalgebra of `R`
have carriers in `Type (max u w)` and can be lifted to this test universe.
The usual set-level all-extension hypothesis is equivalently tested there for
this conclusion: any nilpotence or nonzero witness in a field tensor uses only
finitely many field coefficients, so lies in a finitely generated subextension;
such a subextension has a carrier of size at most `max(#k, aleph_0)` and can be
represented in this universe. Field and tensor isomorphisms preserve reducedness.
There is consequently no restriction on the input algebra universes.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`; its full
  class declaration extends `CommRing` and `DivisionRing`.
- `def-pc-field-extension`: `Algebra`, in `Mathlib.Algebra.Algebra.Defs`; with
  `[Field k] [Field L]`, this supplies exactly the structural ring homomorphism
  `algebraMap k L` into the extension field. The dependency's scheme-theoretic
  explanation of the induced Spec morphism is not an extra hypothesis here.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, defined in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, supplied publicly through
  `Mathlib.RingTheory.TensorProduct.Basic`. This is the quotient by the
  bilinearity relations, not a private copy.

The already recorded proof-dependency modules are imported without `public`:
`Mathlib.Algebra.Module.LocalizedModule.Basic` (`LocalizedModule`),
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.rTensor_exact`,
`Module.Flat.lTensor_exact`, and `Module.Flat.of_free`),
`Mathlib.LinearAlgebra.Basis.VectorSpace` (`Module.Free.of_divisionRing`),
`Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`
(`reduced_noetherian_total_ring_fractions`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.Spectrum.Prime.Noetherian` (the `NoetherianSpace` instance),
and `Mathlib.Topology.NoetherianSpace`
(`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`).
The theorem docstring contains all five DAG proof steps: flat tensor injectivity,
finite-type subalgebra embedding, the finite-product tensor isomorphism, reduced
field factors and injective descent, and finite tensor support for arbitrary `R`.

Edge cases checked mathematically before writing:

- `A = 0` and `R = 0`: the zero ring is allowed as a commutative `k`-algebra;
  its tensor product is the zero ring, which is reduced.
- `R = k` and `A = k`: the conclusion agrees with the standard scalar tensor
  identifications; the hypothesis in particular forces `A` itself to be reduced.
- Reducible reduced `R`, such as `k[x,y]/(xy)`, is allowed; no domain instance
  occurs in the statement.
- Arbitrarily generated polynomial algebras and arbitrary reduced `R` are
  allowed; the proof uses finite support rather than assuming finite generation.
- Characteristic `p` and imperfect `k` are allowed. For example the inseparable
  extension `k = F_p(t)`, `A = k(t^(1/p))` fails the explicit field-extension
  hypothesis after tensoring with itself, so does not give a counterexample.
- An empty finite product of field factors corresponds to the zero ring; the
  proof handles the zero subalgebra directly. Empty tensor sums are zero.

Source verification: read `literature/stacks-project/algebra.tex`, the definition
`definition-geometrically-reduced` and the full statement/proof of
`lemma-geometrically-reduced-any-reduced-base-change` (Tag 034N), together with
`lemma-limit-argument`. The node matches that source. No STATEMENT-DISPUTED issue.

Searches made:

1. `msearch.py ... leanfinder "tensoring a geometrically reduced algebra with any
   reduced algebra over a field yields a reduced ring"`: eight hits, including
   `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`,
   `Algebra.IsGeometricallyReduced`, and
   `IsReduced.tensorProduct_of_flat_of_forall_fg`. None is this theorem: the
   first assumes an algebraic field extension, and the last is a finite-subalgebra
   criterion rather than a reduced-base theorem.
2. `msearch.py ... loogle "Algebra.IsGeometricallyReduced, IsReduced"`: six hits;
   the algebraic extension instance and the algebraic-closure criterion do not
   state the arbitrary reduced algebra result.
3. `msearch.py ... grep
   "IsReduced.*tensor|tensor.*reduced|GeometricallyReduced" RingTheory`: six
   Mathlib hits, in `Nilpotent/GeometricallyReduced.lean` and `Flat/Basic.lean`.
   The pinned geometric-reducedness module still lists the all-field-extension
   comparison as a TODO. No exact match.
4. `rg` on the upstream `WeilConjectures` and side `lean/Sheaf` trees for
   `isReduced_tensorProduct|GeometricallyReduced|geometrically.reduced` and the
   item's exact id. Read the upstream module
   `WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced` in full:
   `isReduced_tensorProduct_of_forall_residueField` assumes reduced tensors at
   every prime of one specific algebra; it is an ingredient, not this statement.
   `isReduced_tensorProduct_of_perfectField` assumes a perfect base field and
   two reduced factors. Existing side statements for separably generated or
   finite separable field extensions likewise have different hypotheses.
   The exact item id has no upstream declaration match.
5. Searched `dag/lean_names_upstream.json` for reduced tensor-product names and
   the side RingTheory/FieldTheory trees for theorem declarations. The selected
   name `isReduced_tensorProduct_of_forall_fieldExtension` is new.

Validation: the Lean file is checked with `scompile.py N9
lem-trf-geometrically-reduced-base-change <file>`; final results are recorded
below after the wrapper completes. The node's `lean.statement` is extracted
verbatim from the theorem keyword to immediately before `:=`; all original node
fields are retained.

`scompile.py` succeeded for the sandbox check and the library module, with no
errors or warnings (reported file times: 25.9 seconds and 13.0 seconds).

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
