## Worker report

The module `Sheaf.Algebra.Lie.RationalHighestWeightModules` states
`LieAlgebra.exists_rational_highestWeight_module`, with `sorry` as the entire
proof. It has no new definitions, helper theorems, or axioms. The accepted
stage-1 split, statement and dependencies are preserved.

The inherited worker ending was a stage-1 live-wins refusal, not a stage-2
failure. The maintenance handoff in brief-stage2 §0 explicitly distinguishes
these stages. The assigned node is split, has no Lean record, and is listed
at stage 2 in the queue. No released repair note for this item was found.

### Hypotheses and clauses

- A finite-dimensional rational Lie algebra is `(g : Type u) [LieRing g]
  [LieAlgebra ℚ g] [FiniteDimensional ℚ g]`. Semisimplicity in the specified
  no-solvable-ideal sense is `[LieAlgebra.HasTrivialRadical ℚ g]`.
- The maximal abelian subalgebra is `H : LieSubalgebra ℚ g`, `[IsLieAbelian H]`
  and `hmax`, asserting that every abelian subalgebra containing H equals H.
  `hsplit` says the sum of ordinary simultaneous adjoint eigenspaces indexed
  by rational linear forms is all of g. This is exactly simultaneous
  diagonalization over ℚ. Independence of distinct eigenspaces is automatic;
  it is not an additional hypothesis. This splitting subalgebra witnesses
  that g is split; there is no algebraic-closure hypothesis.
- `R` with `hR` is exactly the set of nonzero rational adjoint weights,
  characterized by a nonzero ordinary `LieModule.weightSpace`.
- `c : R → H` with `hc` gives the coroot for each root: it belongs to the
  rational span of brackets of opposite ordinary root spaces and its root
  evaluates to 2. These are precisely the node's defining conditions, not
  an arbitrary family of vectors. No root-pairing existence is assumed.
- `Δ : Finset R`, `hbase` and `hcoords` express the simple-root base:
  its roots are rationally linearly independent and every root or its
  negative is a nonnegative integral sum of them. These characterize a
  simple base for the reduced crystallographic adjoint root system here.
- `P : Submodule ℤ (Module.Dual ℚ H)` with `hP` is exactly the integral
  weight lattice: all and only the forms taking integer values on every
  coroot. Taking this already introduced set as a named submodule binder
  makes its type explicit without constructing or duplicating a definition.
- `∃ ω : Module.Basis Δ ℤ P` says the fundamental weights are a ℤ-basis
  of P. The two implications indexed by i,j are exactly the Kronecker-delta
  evaluation `ωᵢ(cⱼ)=δᵢⱼ`. Uniqueness of these weights follows from the
  spanning of the simple coroots and need not be added to the conclusion.
- `∀ lam : P, (∀ i : Δ, 0 ≤ ... (c i)) → ...` quantifies over every
  dominant integral weight, including weights on chamber walls.
- The existential type M, additive group, rational module, Lie ring action
  and Lie-module compatibility give an actual rational representation.
  `FiniteDimensional ℚ M` and `LieModule.IsIrreducible ℚ g M` give finite
  dimension and simplicity. `v ≠ 0` supplies nonzeroness explicitly.
- The equation indexed by `h : H` is the highest-vector weight equation.
  The clause indexed by positive roots, recognized by nonnegative integral
  Δ-coordinates, kills v with every vector of each such root space.
- `LieSubmodule.lieSpan ℚ g {v} = ⊤` is the iterated-product spanning
  clause: the smallest invariant rational subspace containing v is exactly
  the rational linear span of finite iterated g-actions on v, including
  the empty product. No enveloping-algebra choice is introduced.
- `Ω : Finset (Module.Dual ℚ H)` is the finite set of displayed weights;
  membership of lam says its highest weight occurs. The condition for each
  μ in Ω simultaneously says μ is integral and μ = lam minus a
  nonnegative integral sum of simple roots.
- Every displayed ordinary weight space is nonzero. `iSupIndep` and
  `iSup = ⊤` say precisely that these subspaces form an internal direct
  sum. These use ordinary `weightSpace`, never generalized weight spaces.
- All coefficients and eigenvalues throughout are rational. For
  `Subsingleton g` the final implication gives a rational linear
  equivalence `M ≃ₗ[ℚ] ℚ` taking v to 1 and making every Lie action zero.
  This is the stated choice L(0)=ℚ up to the customary identification,
  rather than mere unspecified nonemptiness of a representation.

### Dependency declarations

Both statement dependencies are Mathlib nodes and have no Lean record.
Their recorded matches were read in full:

- `def-wf-lie-algebra`: `LieRing`, `LieAlgebra`, `LieRingModule`, `LieModule`
  in `Mathlib.Algebra.Lie.Basic`; `LieSubalgebra` in
  `Mathlib.Algebra.Lie.Subalgebra`; `LieSubmodule` and
  `LieSubmodule.lieSpan` in `Mathlib.Algebra.Lie.Submodule`;
  `LieModule.IsIrreducible` in `Mathlib.Algebra.Lie.Semisimple.Defs`.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  `Mathlib.Algebra.Lie.Semisimple.Defs` and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` in
  `Mathlib.Algebra.Lie.Semisimple.Basic`.

Additional standard interfaces used directly are `LieModule.weightSpace`
(`Mathlib.Algebra.Lie.Weights.Basic`), `Module.Dual`
(`Mathlib.LinearAlgebra.Dual.Defs`) and `Module.Basis`
(`Mathlib.LinearAlgebra.Basis.Defs`). Their definitions and docstrings were
read. The four proof dependencies have no recorded Lean module; the root-base
node has only Mathlib matches. There is consequently no available owned
proof-dependency module to import. Their full argument is preserved in the
main theorem's docstring for stage 3.

### Edge cases and source reading

The zero Lie algebra is allowed: H=0, R and Δ are empty, P is zero,
the empty fundamental-weight family is a basis, Ω={0}, M=ℚ and v=1.
The cyclic span includes v itself via the empty product. Dominant weights
with zero simple coordinates and lam=0 are included. No irreducibility
assumption is made on the root system or g. An arbitrary ambient universe
u is allowed; every finite rational vector space has a model in Type u,
so the existential representation imposes no size restriction.

Read the actual Milne PDF, Section 23h, printed pages 508 and 511 (PDF pages
520 and 523). Page 508 gives the rational weight gradation, coroot
normalization and the characteristic-zero field extension of the construction;
page 511 invokes the fundamental weights generating P in Corollary 23.73.
As the node explicitly warns, Lemma 22.24 alone is not a highest-weight
existence theorem. The source's missing full split-field theorem is supplied
by the accepted eight-step Verma-quotient proof, reproduced in the Lean docstring.
There is no statement correction and no outstanding statement dispute.

### Searches

Executed the prescribed msearch.py searches for this group and item:

- LeanFinder: “Finite dimensional simple rational highest weight representation
  of split semisimple Lie algebra with all weights integral”. Eight hits:
  the Geck construction irreducibility theorem and existing-weight/generalized
  weight-space infrastructure; none asserts existence for every dominant weight.
- Loogle: “LieModule.weightSpace, LieAlgebra.HasTrivialRadical, RootPairing.Base”.
  No hits for that combined pattern.
- LeanSearch: “Existence of irreducible highest weight rational Lie algebra
  module for every dominant integral weight”. Eight hits, including
  `LieModule.IsIrreducible`, Lie's theorem, and Geck's specific representation;
  none states the item. The relevant definitions were read directly.
- Mathlib grep: `highest.weight|weightSpace|IsMaximalAbelian|IsDiagonalizable`
  in Algebra/Lie. Found ordinary weightSpace and root-space infrastructure;
  no highest-weight module existence theorem.
- Direct rg of WeilConjectures and Sheaf for `highest.weight`,
  `fundamental.weight`, `rationalHighest`, `weightLattice`, and this node id:
  no match. The chosen declaration name was also searched in Mathlib,
  WeilConjectures, Sheaf and dag/lean_names_upstream.json: no match.
- Read `RootPairing.Base`, its weight/coweight bases, the Killing-form coroot
  construction and the ordinary weightSpace definition while selecting the
  interface. A generic root pairing would require extra comparison data;
  the signature instead specifies the given adjoint roots and coroots directly.

### Validation

Every compiler call uses scompile.py against the live published server build.
The first compile found the reserved token λ used as an identifier; renamed
that binder to lam without changing the mathematical statement. Final compile
and the required deliver2.py preflight are recorded by the delivery tool.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
