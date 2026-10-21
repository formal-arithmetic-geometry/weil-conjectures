## Worker report

Item: `lem-sfb-topological-basis-lift-section` (Q67, stage 2).

The module `Sheaf.Topology.TopologicalBasisLiftSection` states
`Module.Basis.exists_continuousLinearMap_section_of_isHomeomorph_equivFun_symm`.
Its sole theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The node is unchanged except for its `lean` record.

Source read: the current blueprint `main-20261015`,
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md`,
“Pushing down by the trace”, particularly the trace/sum map onto the sum lattice.
The node explicitly extracts and supplies the eight-step coordinate argument for
continuous lifting; all eight steps are carried in the theorem's docstring.
No source statement correction is required and no statement dispute was found.

Hypothesis-by-hypothesis correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- A topology on A with continuous addition, negation and multiplication:
  `[TopologicalSpace A] [IsTopologicalRing A]`.
- A-modules M and N, with their topologies:
  `{M : Type v} [AddCommGroup M] [Module A M] [TopologicalSpace M]` and the
  corresponding binders for `{N : Type w}`.
- Continuous module additions, negations and joint scalar actions:
  `[IsTopologicalAddGroup M] [ContinuousSMul A M]` and the analogous N instances.
- A finite index set, possibly empty: `{I : Type t} [Fintype I]`.
  The Fintype instance provides exactly the finite enumeration needed for the sum;
  there is no Nonempty assumption. Every finite set can carry this instance.
- The specified A-basis of N: `(b : Module.Basis I A N)`.
  This is the basis notion in `def-weil-pbc-free-module`, rather than an extra
  abstract freeness assumption or a separately chosen replacement basis.
- The coordinate map beta is a homeomorphism for the product topology:
  `(hβ : IsHomeomorph (b.equivFun.symm : (I → A) → N))`.
  Mathlib's `Module.Basis.equivFun_symm_apply` identifies this particular map with
  `fun a ↦ ∑ i, a i • b i`. The function type has the canonical product topology.
  Its inverse is exactly `b.equivFun`, used in the displayed section formula.
- Continuous, surjective A-linear q: `(q : M →L[A] N)` and
  `(hq : Function.Surjective q)`.
- Any prescribed lifts: `∀ (m : I → M), (∀ i : I, q (m i) = b i) → ...`.
  There is no restriction on the lifts beyond the node's equations.

Conclusion-by-conclusion correspondence:

- Existence of a continuous A-linear section without prescribed lifts:
  `(∃ s : N →L[A] M, Function.RightInverse s q)`, the first conjunct.
- For every prescribed family, the formula defines a continuous A-linear map:
  `∃ s : N →L[A] M, (∀ x : N, s x = ∑ i : I, b.equivFun x i • m i) ∧ ...`.
  The existential supplies a bundled map with precisely that underlying formula,
  not an unspecified choice of section. The sum is the one written in the node.
- `q ∘ s = id_N`: `Function.RightInverse s q`, i.e. `∀ x, q (s x) = x`.
- Prescribed basis values: `∀ i : I, s (b i) = m i`.
- Every topological space Z: `∀ (Z : Type z) [TopologicalSpace Z], ...`.
  The universe z is independent of all module and basis universes.
- Continuous function spaces: Mathlib's `C(Z, M)`, `C(Z, N)` and `C(Z, A)`.
- Pointwise C(Z,A)-module structures: Mathlib's existing
  `ContinuousMap.instSMul'` and `ContinuousMap.module'` are synthesized directly.
  Their scalar action is `(a • f) z = a z • f z`.
- The induced maps are linear over continuous scalar functions:
  `Q : C(Z, M) →ₗ[C(Z, A)] C(Z, N)` and
  `S : C(Z, N) →ₗ[C(Z, A)] C(Z, M)`.
- These are the canonical postcomposition maps:
  `∀ f, Q f = (ContinuousMap.mk q q.continuous).comp f` and
  `∀ f, S f = (ContinuousMap.mk s s.continuous).comp f`.
  These equations completely characterize the maps; no arbitrary replacement map
  or extra splitting hypothesis is substituted for the canonical construction.
- Surjectivity and linear right inverse: `Function.Surjective Q ∧
  Function.RightInverse S Q`.
- Every continuous map Z' to Z: `∀ (Z' : Type z') [TopologicalSpace Z']
  (a : C(Z', Z)), ...`. The second space's universe z' is also independent.
- Commutation with precomposition for q_*:
  `∀ f, (ContinuousMap.mk q q.continuous).comp (f.comp a) = (Q f).comp a`.
- Commutation with precomposition for s_*:
  `∀ f, (ContinuousMap.mk s s.continuous).comp (f.comp a) = (S f).comp a`.
  The left sides explicitly use the same canonical postcomposition at Z', rather
  than introducing another chosen map. The formula characterizing Q/S above
  identifies these with the induced maps on any primed space. Precomposition on
  the scalar ring is likewise Mathlib continuous-map composition, so this is the
  stated naturality with scalar restriction, without claiming same-ring linearity
  of a map between the two different rings C(Z,A) and C(Z',A).

Dependency declarations read and used:

- `def-weil-pbc-free-module` records `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic`. The source class and docstring were
  read: freeness is existence of an indexed `Module.Basis`, exactly as the node
  specifies. The dependency module is publicly imported. Since this item already
  supplies a particular basis, the statement uses that dependency's underlying
  `Module.Basis` notion, not a redundant `[Module.Free A N]` instance.
- `Module.Basis` and `Module.Basis.equivFun` from
  `Mathlib.LinearAlgebra.Basis.Defs` (imported by the dependency above). The basis
  structure is an equivalence to finitely supported coefficients; for finite I,
  `equivFun` is its equivalence with all functions on I.
- `IsHomeomorph` from `Mathlib.Topology.Homeomorph.Defs`.
- `ContinuousMap.module'`, continuous-map composition and continuous linear maps,
  available through `Mathlib.Topology.ContinuousMap.Algebra`.

Edge cases checked mathematically before writing:

- I empty: the basis forces N to be zero, the section formula is the empty sum,
  and no lift is chosen. All displayed conclusions still hold.
- N zero: the statement only requires a supplied basis; there is no positive rank
  or nontriviality assumption. Over a nonzero ring this permits the empty basis.
- A the zero ring: modules are trivial, even a nonempty finite basis can have its
  usual coordinate meaning, and all formulas still hold. No Nontrivial A instance.
- Empty Z or Z': continuous function identities are pointwise and remain valid;
  the continuous function ring on empty Z can be the zero ring.
- No Hausdorff, completeness, norm, field, compactness or non-discrete assumption
  is imposed. M, N, I, Z and Z' have separately bound universes.

Searches (all through the prescribed msearch.py wrapper where indicated):

- LeanFinder query: “A continuous linear surjection onto a topologically finite
  free module over a topological commutative ring splits by arbitrary chosen basis
  lifts, naturally on continuous function modules”. Eight hits, led by
  `LinearMap.splittingOfFunOnFintypeSurjective`, its splitting lemmas, and
  `ContinuousLinearMap.exists_right_inverse_of_surjective`. No exact match.
- Loogle query: `Module.Basis, Continuous`. Four hits: `continuous_equivFun_basis`,
  `Module.Basis.continuous_toMatrix`, `Module.Basis.continuous_coe_repr` and an
  unrelated box-integral limit. No exact match.
- Mathlib grep query: `constrL|equivFunL|postcomp|compLeftContinuous`, restricted to
  `Topology/Algebra`. Found basis constructors, function postcomposition and
  uniform-convergence interfaces, not the full statement.
- LeanSearch query: “A continuous linear surjection onto a finite free module over
  a topological ring with homeomorphic coordinates admits a section specified by
  any basis lifts and induces a split surjection on continuous function modules”.
  Eight hits, including algebraic splittings, `Module.Basis.constrL`, and normed
  open/quotient-map results. No exact match.
- Read the relevant source signatures, not only search descriptions:
  `Mathlib/LinearAlgebra/Finsupp/Pi.lean:171-185` gives algebraic splitting only;
  `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:434-455` has `constrL` and
  `equivFunL` over a nontrivially normed field, unlike this topological-ring lemma.
- Project rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `topological.basis|basis.lift|basis.*section|continuous.*[Ll]ift|compLeftContinuous`
  found unrelated sheaf basis constructions and ring-map postcomposition.
  An exact search of the item id and proposed declaration name in both libraries
  and `dag/lean_names_upstream.json` returned no match. No duplicate declaration.

Validation: the prescribed `scompile.py Q67 lem-sfb-topological-basis-lift-section`
compiled this file as both a sandbox module (5.6 seconds) and its actual module
(2.8 seconds), with no errors or warnings. The source has no lines over 100
characters, every universe and variable is bound, and the only postponed proof is
the named theorem corresponding exactly to this DAG node.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
