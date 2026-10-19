## Worker report

Repair of the returned stage-2 delivery at immutable head bfaf56797a7f.
The retained sandbox contained only dispatcher marker files, so this repair supplies the
missing packet rather than re-pushing the stage-1 report.

The module `lean/Sheaf/RingTheory/ValuationDomainFibreDimensions.lean` states
`ValuationRing.finiteType_domain_fibre_dimensions`, with a single `sorry` proof.
It states both conclusions of Stacks Project, Algebra, Tag 00QK
(`literature/stacks-project/algebra.tex`, lines 31379–31409), including the final
assertion about every irreducible component. The declaration docstring contains all
eight proof steps of the current node, with the dependencies used in each step.
No definition or auxiliary theorem is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A is a valuation ring, in particular an integral domain | `(A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]` |
| For every nonzero element of Frac(A), it or its inverse lies in A | Mathlib `ValuationRing A`; `ValuationRing.TFAE A` identifies this with the fraction-field formulation |
| K = Frac(A) | `FractionRing A`, the localization at `nonZeroDivisors A` |
| k = A / m_A | `IsLocalRing.ResidueField A`, definitionally `A ⧸ IsLocalRing.maximalIdeal A`; the local-ring instance follows from the valuation-ring instance |
| D is an integral domain | `(D : Type v) [CommRing D] [IsDomain D]` |
| D contains A as a subring | `[Algebra A D]` and `(hAD : Function.Injective (algebraMap A D))` |
| D is finite type over A | `[Algebra.FiniteType A D]` |
| D_k = D tensor_A k | `D ⊗[A] IsLocalRing.ResidueField A` |
| D_K = D tensor_A K | `D ⊗[A] FractionRing A` |
| Tensor multiplication (d tensor a)(e tensor b) = de tensor ab | The canonical `CommRing` structures from `Mathlib.RingTheory.TensorProduct.Basic`, whose pure-tensor multiplication is `Algebra.TensorProduct.tmul_mul_tmul` |
| D_k is not the zero ring | `[Nontrivial (D ⊗[A] IsLocalRing.ResidueField A)]` |
| dim D_k = dim D_K | First conjunct, the equality of the two `ringKrullDim` terms |
| Spec D_k | `PrimeSpectrum (D ⊗[A] IsLocalRing.ResidueField A)`, the underlying Zariski space of `AlgebraicGeometry.Spec (CommRingCat.of ...)` |
| Every irreducible component of Spec D_k | `∀ Z : Set (PrimeSpectrum ...), Z ∈ irreducibleComponents (PrimeSpectrum ...) → ...` |
| Its topological Krull dimension equals dim D_K | `topologicalKrullDim Z = ringKrullDim (D ⊗[A] FractionRing A)` |

The dimensions have Mathlib's common type `WithBot ℕ∞`, retaining both the empty
case convention and unbounded dimensions. The subtype `Z` carries the subspace topology.
The component conclusion is not an irreducibility assertion about the special fibre.
Universes `u v` are explicitly bound and independent; the field types are canonical
constructions from `A`. `set_option autoImplicit false` rules out unbound implicits.
There are no rank, discreteness, Noetherian, flatness, or field-characteristic assumptions.

All six statement dependencies were opened, including their recorded Mathlib signatures
and docstrings:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; the algebra multiplication is supplied by
  `Mathlib.RingTheory.TensorProduct.Basic` on this same tensor product.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`; its underlying space is `PrimeSpectrum` with precisely
  its Mathlib Zariski topology, used directly because the conclusion is topological.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`, the maximal irreducible subsets.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, applied to each component subtype.

The public imports give these notions and the valuation-ring and residue-field constructions.
The following already-stated proof dependencies are imported without `public`:

- `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`:
  `finiteType_domain_ringKrullDim_eq_trdeg`.
- `Sheaf.RingTheory.DimensionAtPointComponents`:
  `AlgebraicGeometry.dimension_at_point_components`.
- `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`:
  `Algebra.fibre_dimension_bounded_open_upstairs`.
- `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra`:
  `Algebra.exists_quasiFinite_over_polynomial_algebra`.
- `Sheaf.RingTheory.QuasiFiniteFourRings`:
  `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`:
  `IsOpen.topologicalKrullDimAt_eq`, `topologicalKrullDimAt`.
- `WeilConjectures.Topology.DimensionSupremumLocalDimensions`:
  `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`. Its current source was read using
  `scompile.py --source`, because it was absent from the older local source checkout.

The remaining proof dependencies have Mathlib matches, except
`lem-trf-quasi-finite-polynomial-kernel-dimension-drop`, which has no recorded Lean
module yet and is therefore not imported. That is a future proof input, not a notion
needed to state this item. No import cycle was found or avoided by omitting a stated module.

Edge cases checked before and after writing:

- A field is permitted as a valuation ring: its maximal ideal is zero and the residue and
  fraction fields identify with A; the theorem reduces to the identical finite-type algebra.
- D = A is permitted, as is relative dimension zero; both fibres are fields, of dimension zero.
- The zero ring is excluded for A and D exactly by the domain assumptions. A nonzero domain
  D can nevertheless have zero special fibre (for example invert a nonzero element of m_A).
  The separate `Nontrivial` special-fibre hypothesis is thus necessary and exactly the source's.
- Arbitrary-rank and non-Noetherian valuation rings are covered: no DVR or dimension-one
  hypothesis was added. Both equal and mixed characteristic are allowed.
- A reducible or nonreduced special fibre remains permitted. The quantified component clause
  specifies the dimension of each component separately, and does not impose `IsDomain` on it.
- Independent universes for A and D do not restrict the finite-type algebra or its spectra.

Searches for an existing statement (2026-10-18 UTC):

- `msearch.py ... leanfinder "A finite type domain containing a valuation ring has
  equidimensional nonempty closed fibre of the same dimension as its generic fibre"`:
  eight hits concerning Dedekind domains/DVRs, cotangent rank, and ring dimension bounds;
  no closed/generic-fibre comparison for an arbitrary valuation ring.
- `msearch.py ... loogle "ValuationRing, ringKrullDim"`: zero hits.
- `msearch.py ... leansearch "Equality of special and generic fibre dimensions for a finite
  type domain over a valuation ring and equidimensionality of the closed fibre"`: eight
  hits, including `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, ring-equivalence
  invariance, and DVR/cotangent lemmas; no statement matching 00QK.
- `msearch.py ... grep "valuation.*(dimension|dim_fib)|equidimensional|dim.*valuation"`:
  eight hits, involving coevaluation, cycle commentary, DVRs and Dedekind valuations;
  no matching fibre theorem.
- `rg -n` with that expression and the proposed declaration name in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: relevant hits are DVR dimension facts and neighbouring
  geometric equidimensionality nodes, not this theorem; the proposed full name is unused.
- `grep -rn "lem-trf-valuation-domain-fibre-dimensions"` in upstream `WeilConjectures`:
  no hits. In the shared side source the item appears in a consumer's proof docstring,
  not as a declaration of its own.

Repair accounting:

- H1: the packet now contains the actual Lean module, this Worker report, and the second
  reading below. It claims no `citations.json` or extra helper node; neither is needed.
- H2: the item now has the complete `lean` record and verbatim signature. It was reconstructed
  from the current shared node, preserving every non-`lean` field, in particular the current
  stage-1 `split_report.summary` and the eight-step proof landed by Q140. No stage-1 field is
  edited by this packet. `deliver2.py` rebases the field delta on current `newtargets-dag`.
- The supplied correction request's exact ring assumptions, injective map, special-fibre
  nontriviality, ring-dimension equality and every-component topological dimension are present.
- The module was compiled by the required `scompile.py` wrapper: exit 0; sandbox compile
  4.3 seconds, library module compile 2.7 seconds; no diagnostics. One theorem remains
  deliberately `sorry`, as required in stage 2.

No statement correction, disputed assertion, new node, or dependency-interface repair is needed.

## Second reading by Q49

After the successful compile, I reopened the node and module and compared the statement from
scratch against Stacks 00QK and all six statement dependency definitions. This is a separate
rereading by the same dispatcher worker, not a claim to a second agent's independent review;
the repair brief prohibits starting other agents and reserves independent review to the maintainer.

The binders cover a valuation domain A and a finite-type domain algebra D. The explicit
injectivity of `algebraMap A D` is the source's containment assumption. `IsLocalRing.ResidueField A`
is precisely A/m_A under Mathlib's valuation-induced local structure; `FractionRing A` is Frac(A).
Neither field is an arbitrary replacement. Mathlib's tensor-product ring is the tensor algebra
with the displayed multiplication, rather than a second construction. Nontriviality is imposed
on D tensor k, not on an unrelated algebra. The first conjunction equates exactly the two ring
Krull dimensions. The second quantifies over all maximal irreducible subsets of the actual prime
spectrum of D tensor k, and takes their subspace topological Krull dimensions, comparing them
with the same generic ring dimension. There is no additional finiteness, domain, closedness,
or irreducibility hypothesis on these components or on the special fibre.

No mathematical mismatch was found on this second pass. The returned packet's missing module,
missing Lean record and missing stage-2 report have been repaired, and its unauthorized stage-1
summary delta is absent. The theorem is the only declaration and its proof is exactly `by sorry`.
The docstring records the eight current proof steps; all stated non-Mathlib proof dependencies
are imported. The node signature is extracted verbatim from the file, and all non-`lean` node
fields were compared to current shared main and found identical.
