## Worker report

The module `Sheaf.Algebra.Lie.IntegrableUpperBoundedWeightFiniteness` states
`LieAlgebra.finite_weights_and_finiteDimensional_of_integrable_upperBounded`.
Its only theorem has proof `sorry`; the docstring carries all seven steps of the node's proof.
No definitions or auxiliary nodes are needed. The node is changed only in `lean`.

Correspondence with the statement, hypothesis by hypothesis:

- The finite-dimensional rational Lie algebra is `g : Type u`, `[LieRing g]`,
  `[LieAlgebra ℚ g]`, and `[FiniteDimensional ℚ g]`. Semisimplicity in the node's
  no-solvable-ideal sense is `[HasTrivialRadical ℚ g]`.
- The splitting maximal abelian subalgebra is `H : LieSubalgebra ℚ g`,
  `[IsLieAbelian H]`, `hmax`, and `hsplit`. The latter says each adjoint operator
  has eigenspaces over ℚ spanning `g`, exactly diagonalizability. This is the
  same hypothesis used in the recorded root-decomposition theorem.
- `R : Set (Module.Dual ℚ H)` and `hR` specify exactly the nonzero weights with
  nonzero ordinary root spaces. `LieModule.weightSpace` is the intersection of
  the eigenspaces and its membership theorem says precisely
  `∀ h, ⁅h,m⁆ = μ h • m`.
- `c : R → H` and `hc` specify the coroots: membership in the span of brackets
  from the opposite root spaces and evaluation two. By the recorded
  root-decomposition theorem this span is a line and there is a unique such
  Cartan element, so these are exactly its coroots, rather than extra arbitrary
  data or a different pairing. No additional structural conclusion of that
  theorem is required as a hypothesis here.
- `Δ : Finset R`, `b : Module.Basis Δ ℚ (Module.Dual ℚ H)`, `hb`, and `hcoords`
  express a simple-root base. The basis vectors are exactly the selected roots;
  every root has integral coordinates of one sign. This matches the base
  convention in the dependency node (its additive-monoid closure formulation
  is equivalently the finite natural-coefficient sums used here).
- `e f : Δ → g`, `he`, `hf`, and `hef` say that both chosen vectors are nonzero,
  in the indicated positive and negative ordinary root spaces, and that their
  bracket is the specified coroot. Rank-one relations are consequences of these
  assumptions, rather than added assumptions.
- The arbitrary rational representation is `M : Type v` with `[AddCommGroup M]`,
  `[Module ℚ M]`, `[LieRingModule g M]`, `[LieModule ℚ g M]`. The separate universe
  `v` is unrestricted. There is no ambient finiteness or cyclicity hypothesis.
- The ordinary weight decomposition is `hdecomp : DirectSum.IsInternal ...`
  indexed by all `Module.Dual ℚ H`. This is bijectivity of the canonical sum of
  submodule inclusions, hence both spanning and directness, not a generalized
  weight decomposition. Every weight space is finite-dimensional by `hfinite`.
- The finite upper set is `A : Finset (Module.Dual ℚ H)`. `hupper` expresses the
  support containment clause by clause: each nonzero weight is some `η ∈ A`
  minus a sum of simple roots with coefficients `n : Δ → ℕ`. The coefficients
  are natural integers, not arbitrary nonnegative rational coefficients.
- `he_nil` and `hf_nil` quantify over each simple root and each vector, with a
  positive natural exponent making the corresponding power of `LieModule.toEnd`
  vanish on that vector. The exponent may depend on the vector; no uniform
  nilpotence is imposed.
- The first conclusion is `.Finite` for precisely the set of linear weights
  whose ordinary weight spaces are not bottom. The second is
  `FiniteDimensional ℚ M`. Both are asserted as a conjunction.

Dependency declarations read and used:

- `def-wf-lie-algebra`: Mathlib's `LieRing`, `LieAlgebra`, `LieRingModule`,
  `LieModule` in `Mathlib.Algebra.Lie.Basic`, and `LieModule.toEnd` /
  `LieAlgebra.ad` in `Mathlib.Algebra.Lie.OfAssociative`. These give the original
  bracket and representation, including their compatibility identities.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  `Mathlib.Algebra.Lie.Semisimple.Defs`, with
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` in
  `Mathlib.Algebra.Lie.Semisimple.Basic`. The recorded upstream wrapper
  `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot` in
  `WeilConjectures.Mathlib.Algebra.Lie.Radical` was also read; it is the same
  predicate/equivalence, so no new specialization module is needed.
- `lem-sfb-split-semisimple-root-decomposition`:
  `LieAlgebra.exists_splitSemisimple_rootDecomposition` in
  `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`, publicly imported.
  Its full statement and proof-plan docstring were read; the maximal abelian,
  splitting, root-set, coroot and simple-base interfaces above follow it.
- Its public imports supply `LieModule.weightSpace` and
  `LieModule.mem_weightSpace` (`Mathlib.Algebra.Lie.Weights.Basic`),
  `DirectSum.IsInternal` (`Mathlib.Algebra.DirectSum.Basic`), and `Module.Basis`.
- The proof-only dependency `lem-sfb-integrable-sl2-reflection-automorphism`
  currently has no Lean record or upstream audit; therefore no nonexistent
  module is imported. Its precise role is retained in step 3 of the docstring.
  No statement depends on an unstated exponential construction.

Edge cases checked before writing:

- Empty `A`: `hupper` rules out every nonzero weight space; `hdecomp` then
  forces `M = 0`. The finite support and finite dimension conclusions hold.
- Zero Lie algebra / rank zero: no nonempty assumptions occur on `g`, `H`, `R`
  or `Δ`. The empty basis forces the dual to be zero. The module consists of
  its zero-weight space, finite-dimensional by `hfinite`. Its action and the
  local-nilpotence conditions have the intended vacuous or zero interpretations.
- The zero module is allowed and has empty support; all weight spaces are zero.
- `n = 0` is explicitly excluded in local nilpotence by `0 < n`.
- Nonintegral rational weights and arbitrary cardinality of `M` are allowed:
  only the downward differences are integral, and no `FiniteDimensional ℚ M`
  instance appears among the assumptions. Infinite-dimensional zero-action
  modules fail `hfinite` at the zero weight, as they must.

Searches (all 2026-10-24):

- `msearch.py leanfinder`: “An integrable upper bounded weight module with finite
  dimensional weight spaces for a split semisimple rational Lie algebra has
  finite support and is finite dimensional”. Eight hits, including
  `LieModule.Weight.instFinite`, `finite_genWeightSpace_ne_bot`, and
  `iSup_genWeightSpace_eq_top`. Inspection of their full declarations shows
  that the finiteness results assume `[IsNoetherian R M]` (already finite
  dimension over ℚ), and decomposition results assume finite dimension.
- `msearch.py loogle`: `LieModule.weightSpace, Module.Finite`. Three hits:
  existence of a nontrivial weight space under nilpotent/solvable/ideal
  hypotheses, all requiring finite-dimensional ambient representations.
  None is this criterion.
- `msearch.py grep`: `integrable|locally.nilpotent|finite_genWeightSpace|def
  weightSpace|def IsInternal`, restricted to `Algebra/Lie`. Eight hits, giving
  the existing ordinary weight-space definition and the same Noetherian
  generalized-weight finiteness results; no integrability criterion.
- `msearch.py leansearch`: “An integrable weight module with finite dimensional
  weight spaces and weights in finitely many downward simple root cones is
  finite dimensional”. Eight hits, again weight-space notions and finiteness
  under ambient Noetherian hypotheses. Reused the ordinary weight-space
  definition; did not replace it with `genWeightSpace` or `Weight`.
- `rg` in project `WeilConjectures/` and `Sheaf/` for `integrable`,
  `upper[Bb]ounded`, `weightSpace`, and `locallyNilpotent`: the highest-weight
  module docstring cites this missing criterion, and nearby modules use
  ordinary weight spaces. No existing statement matches this node.
- The item-id search in `WeilConjectures/` has no hits. The chosen full theorem
  name was searched in Mathlib, `WeilConjectures/`, `Sheaf/`, and the upstream
  name index without a collision. A Mathlib search for `IsLocallyNilpotent` /
  `locallyNilpotent` in the relevant linear/Lie directories found no matching
  predicate; pointwise local nilpotence is expressed directly.

Source check: read Milne's printed pp.508–511 (PDF pages 520–523), including
rational-field extension, normalized opposite root vectors, rational weight
gradations and Corollary 23.73. As the node explicitly says, Milne supplies
background, not this general infinite-dimensional criterion. The proof in the
node is the agent's seven-step generalization, reproduced in the docstring.
There is no statement correction, disputed assertion, or missing notion.

Validation: `scompile.py Q19 lem-sfb-integrable-upper-bounded-weight-finiteness`
compiled the module against the published library with no errors or unexpected
warnings. Delivery dry run and push follow this compile.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
