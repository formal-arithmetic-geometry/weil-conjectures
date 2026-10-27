## Worker report

The module `Sheaf.RingTheory.PolynomialZeroSectionDimension` states
`AlgebraicGeometry.topologicalKrullDimAt_polynomial_zero_section`, with its sole
proof postponed by `sorry`. No definitions, new nodes, dependency repairs, or
statement corrections are needed. The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`.
- The finite type commutative k-algebra is `{B : Type v} [CommRing B]
  [Algebra k B] [Algebra.FiniteType k B]`. Universes u and v are independent.
- The nonnegative number of variables is `(r : ℕ)`; the algebra C is the exact
  Mathlib polynomial ring `MvPolynomial (Fin r) B`. Reindexing variables from
  1,...,r to Fin r has no mathematical effect and includes r = 0.
- The prime ideal q is represented by its corresponding point
  `(q : Spec (CommRingCat.of B))`. The underlying type of this affine scheme is
  `PrimeSpectrum B`, whose elements carry precisely a prime ideal and primality.
- The specified Q is `PrimeSpectrum.comap
  (MvPolynomial.eval (fun _ : Fin r ↦ (0 : B))) q`. This is literally the inverse
  image prime under evaluation at zero, one of the node's two equivalent
  descriptions. The canonical construction supplies primality without a new
  hypothesis or postponed helper. Its ideal consists of polynomials with constant
  coefficient in q, equivalently qC plus the variable ideal.
- The two affine spectra are explicitly `Spec (CommRingCat.of B)` and
  `Spec (CommRingCat.of (MvPolynomial (Fin r) B))`.
- Both dimensions use the recorded `topologicalKrullDimAt`, the infimum of
  topological Krull dimensions of open neighbourhoods, not local-ring dimension.
- `∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧
  topologicalKrullDimAt ... = ((d + r : ℕ) : WithBot ℕ∞)` expresses exactly that
  both dimensions are finite nonnegative integers and the latter is the former
  plus r. Once the first dimension is d, d+r is a natural number as well; these
  two equalities are equivalent to the node's finiteness and dimension formula.
- There is no reducedness, equidimensionality, perfectness, characteristic,
  nontriviality, or maximality assumption. In the zero ring there is no possible
  q, so the theorem is vacuous as required.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` (the node's mathlib_match)
  and `RingHom.FiniteType` (its lean record). The algebra formulation here is
  exactly finite type of the given k-algebra; no replacement definition is made.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and
  `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`:
  `MvPolynomial.aeval` and `MvPolynomial.eval`. The statement uses the existing
  evaluation ring homomorphism at the zero valuation.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- The standard point preimage is `PrimeSpectrum.comap` from
  `Mathlib.RingTheory.Spectrum.Prime.RingHom`, available through Scheme.

The already stated proof dependencies are imported with plain `import`:
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic` (`Ideal.exists_minimalPrimes_le`),
`Mathlib.RingTheory.KrullDimension.Basic` (`ringKrullDim`),
`Mathlib.RingTheory.KrullDimension.Polynomial`
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`), and
`WeilConjectures.RingTheory.DimensionAtPointComponents`
(`AlgebraicGeometry.dimension_at_point_components`). The polynomial-domain instance
is in the publicly imported Basic module; finite-type Noetherianity is
`Algebra.FiniteType.isNoetherianRing` in the publicly imported FiniteType module.
All four proof steps are reproduced in the theorem docstring.

Sources read: Stacks `literature/stacks-project/algebra.tex`, Tag 00OT,
`lemma-dimension-at-a-point-finite-type-over-field` (lines 27787ff), and Tag 00P0,
`lemma-dimension-prime-polynomial-ring` (lines 28178ff). The former identifies
open-neighbourhood dimension with the maximum dimension of components through the
point; the latter gives the finite domain component dimension. The recorded
polynomial-dimension theorem supplies the componentwise increase by r.

Edge cases checked mathematically:

- r = 0: the empty-variable polynomial ring is B, evaluation is its canonical
  identification with B, and the conclusion reads d = d + 0.
- B = 0: no point of Spec B exists; no excluded nontriviality assumption is needed.
- B = k[t], q = (0): the base open-neighbourhood dimension is 1, though its
  local-ring dimension is 0; the theorem gives 1+r and uses the correct notion.
- B = k[ε]/(ε²): nilpotents do not change the spectrum; the dimensions are 0 and r.
- Unequal-dimensional components, for example
  k[u,v,w]/((u) ∩ (v,w)) at the prime (v,w): only the one-dimensional component
  passes through the point, so the answer is 1+r, not global dim B+r = 2+r.
- Arbitrary fields, including imperfect fields, and nonmaximal q are permitted.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "The topological dimension at the zero
  section prime of a polynomial algebra over a finite type field algebra is the
  dimension at the base prime plus the number of variables": 8 hits, including
  global polynomial dimension, lower bounds, and standard-smooth relative
  dimension. None is this pointwise statement with its finite type base algebra.
- `msearch.py ... loogle 'MvPolynomial, "topologicalKrullDimAt"'`: 0 hits.
- `msearch.py ... grep 'topologicalKrullDimAt|zeroSection|dimensionAtPoint'
  RingTheory`: 0 hits in Mathlib.
- `msearch.py ... leansearch` with query "Dimension at a zero section point of a
  polynomial algebra equals the topological dimension at the base prime plus
  number of variables": 8 hits, including global polynomial dimension and
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, none this assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `topologicalKrullDimAt|polynomial_zero_section_dimension|zeroSection`, followed
  by focused searches for polynomial point-dimension statements: existing local
  dimension definitions, field-extension invariance, polynomial quotients over
  fields, affine-space zero-section geometry, and related fibre-dimension
  statements. Read the relevant signatures in
  `PolynomialQuotientDimensionAtPointHeightDifference.lean` and
  `DimensionAtPointFieldExtension.lean`; neither states this node. Their quotient
  or field-extension hypotheses/conclusions differ.
- `rg -n 'lem-sfb-polynomial-zero-section-dimension' lean/WeilConjectures`: no hit.
  The proposed full declaration name also has no existing hit in either library.

Validation: prescribed `scompile.py Q96 lem-sfb-polynomial-zero-section-dimension`
compiled both sandbox and library forms cleanly (3.2 s and 1.2 s respectively).
`set_option autoImplicit false` enforces explicitly bound variables.
There is no STATEMENT-DISPUTED issue or source/node fault.

## Second reading by Q96

A separate rereading of the node and completed module was performed in this worker
session; no additional agent was started, as instructed by the dispatcher brief.
The external independent reading is the maintainer's review.

The field, finite type algebra, number of variables, and arbitrary prime are the
four binders described above. The upstairs point is the actual canonical inverse
image under evaluation, with no free auxiliary map or new assumption. The explicit
ambient Spec in the second dimension ensures it is measured in the polynomial
spectrum. The first equality fixes the base dimension to a natural d; the second
makes the polynomial dimension d+r. This simultaneously preserves the formula
and both finiteness clauses. In particular, the finite type assumption was not
silently replaced by Noetherianity, and the prime was not made maximal. Zero
variables, zero algebra, nonreduced algebras, and components of differing dimensions
are retained. All statement dependencies use existing recorded notions. The
proof-only imports are kept private. No mismatch was found and no statement
change was made.
