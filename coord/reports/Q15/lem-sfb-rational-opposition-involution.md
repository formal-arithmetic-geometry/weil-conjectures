## Worker report

The module `Sheaf.Algebra.Lie.RationalOppositionInvolution` states
`LieAlgebra.exists_rational_opposition_involution`. Its sole theorem has proof `sorry`;
there are no definitions, additional theorems, new nodes or dependency repairs. The node
copy changes only `lean`; the natural-language statement and dependency lists are unchanged.

Source read: Milne, Algebraic Groups (2017), Section 23h, printed pp.503–504 and p.508.
The text defines a splitting Cartan subalgebra as a maximal abelian subalgebra with
rationally diagonalizable adjoint operators. The p.508 opposition signs give minus the
normalized negative simple generator and minus one on the Cartan. The rational descent
is the agent-stated generator-relations argument recorded in the DAG, not a quoted
rational-field theorem. I also read the current blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` through `literature/blueprint/latest`;
this supporting assertion changes neither that unit nor its route.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A rational Lie algebra | `(L : Type u) [LieRing L] [LieAlgebra ℚ L]` |
| Finite-dimensional | `[FiniteDimensional ℚ L]` |
| Semisimple: no nonzero solvable ideal | `[HasTrivialRadical ℚ L]`, using the dependency's Mathlib match |
| A subalgebra of the given algebra | `(H : LieSubalgebra ℚ L)` |
| Abelian | `[IsLieAbelian H]` |
| Maximal among abelian subalgebras | `hmax`: every abelian `A` containing `H` equals `H` |
| Acts diagonally over the rationals | `hsplit`: the supremum of the rational eigenspaces of every `ad ℚ L h` is top |
| The reduced crystallographic root system in the dual of `H` | `(I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)` with `[P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]` |
| Its pairing is evaluation | `heval`: `P.toLinearMap α h = α h` |
| The actual root spaces are the simultaneous eigenspaces | `LieModule.weightSpace L (P.root i)`; its membership equation is Mathlib's `LieModule.mem_weightSpace` |
| The given internal root decomposition | `hdecomp : DirectSum.IsInternal (Sum.elim ... ...)`, with a single `Unit` summand for `H` and all root spaces indexed by `I` |
| One-dimensional root spaces | `hdim`: their rational `Module.finrank` is one |
| The coroot belongs to the bracket span of the opposite spaces | `hcoroot`: membership in the rational span of all brackets of a vector in weight `P.root i` and a vector in weight `-P.root i` |
| Coroot lies in `H` and evaluates to two | `P.coroot i : H`, and `P.root_coroot_two` together with `heval` gives `(P.root i) (P.coroot i) = 2` |
| A subset of roots forming a basis of the dual | `(Δ : Set I) (b : Module.Basis Δ ℚ (Module.Dual ℚ H))`, and `hb` identifies each basis vector with its root |
| Every root has integral coordinates of one sign | `hsign`: the root or its negative belongs to `AddSubmonoid.closure (P.root '' Δ)` |
| Prescribed simple-root vectors | `(x : Δ → L)` and `hx`: membership in their specified root spaces |
| Each prescribed vector is nonzero | `hxne : ∀ i : Δ, x i ≠ 0` |
| Existence of a rational linear Lie automorphism | `∃ θ : L ≃ₗ⁅ℚ⁆ L` |
| Its square is the identity | `Function.Involutive θ` |
| It acts by minus one on `H` | `∀ h : H, θ (h : L) = -(h : L)` |
| Equality of the image of every root space with its opposite | `Submodule.map θ.toLinearEquiv.toLinearMap ... = (LieModule.weightSpace L (-P.root i)).toSubmodule` |
| Prescribed normalization | `∀ i : Δ, ⁅x i, -θ (x i)⁆ = (P.coroot i : L)` |
| Empty base included | No nonemptiness instance on `I` or `Δ`; `Δ` is an arbitrary set |

`I` is an arbitrary finite indexing type for the root set, so it does not choose an
enumeration or identify roots that were distinct. The embedding `P.root` identifies
the node's set `R` with `Set.range P.root`. Its roots are nonzero, as their evaluation
on their coroot is two. The decomposition and one-dimensionality make these exactly
the occurring nonzero weights. This matches the same parametrization in the existing
consumer `LieAlgebra.exists_chevalley_basis_of_pinning` and in the root decomposition
proof dependency. The coroot normalization is part of `RootPairing`, not an additional
assumption about an unrelated family. The bracket span is the `[I,J]` notion in
`def-wf-lie-algebra`. Finite sums of simple roots, represented by additive-submonoid
closure, are exactly their nonnegative integral combinations; uniqueness of the basis
coordinates makes the sign condition exact. No choice of negative simple generators
or a Lie-algebra presentation is assumed by the statement.

Dependency declarations read and used:

- `def-wf-lie-algebra` has a Mathlib match rather than a `lean` record. The statement
  uses `LieRing`, `LieAlgebra`, `LieSubalgebra` and `LieAlgebra.ad` from
  `Mathlib.Algebra.Lie.Basic`, `Mathlib.Algebra.Lie.Subalgebra` and
  `Mathlib.Algebra.Lie.OfAssociative`, exposed by the public Mathlib imports.
- `def-wf-semisimple-lie-algebra` likewise has a Mathlib match. Its predicate is
  `LieAlgebra.HasTrivialRadical` in `Mathlib.Algebra.Lie.Semisimple.Defs`.
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` in
  `Mathlib.Algebra.Lie.Semisimple.Basic` gives exactly the node's definition;
  I read the full class definition, equivalence signature and docstrings.
- The already stated proof dependency `lem-sfb-split-semisimple-root-decomposition`
  is imported privately as `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`;
  I read its full `LieAlgebra.exists_splitSemisimple_rootDecomposition` signature
  and proof docstring. Its ordinary weight spaces, evaluation pairing, bracket
  span and root-basis conventions match this statement.
- The Mathlib proof dependency `lem-sfb-root-base-rational-integral-spans` is imported
  privately through `Mathlib.LinearAlgebra.RootSystem.BaseExists`. I read the recorded
  `RootPairing.Base.mk'`, `RootPairing.Base.toWeightBasis`,
  `RootPairing.Base.toCoweightBasis`, `RootPairing.Base.span_int_root_support`, and
  `RootPairing.Base.span_int_coroot_support` definitions/signatures and docstrings.
- `lem-sfb-pinned-serre-presentation-isomorphism` has no recorded Lean declaration
  or Mathlib match. It is needed only by the later proof, and introduces no notion
  required to type this statement. It remains named in the complete proof docstring;
  there is no nonexisting module to import. No prerequisite is assumed or replaced.

The public mathematical notions beyond those dependency matches are all existing
Mathlib notions: `RootPairing`, its root-system/reduced/crystallographic predicates,
`Module.Basis`, `LieModule.weightSpace`, `DirectSum.IsInternal`, `LieEquiv`, and
`Submodule.map`. There is no missing notion requiring a new definition node.

Edge cases checked before writing:

- Empty `Δ`: its basis makes `Module.Dual ℚ H` zero; finite-dimensional duality gives
  `H = 0`. A root cannot occur in a zero space since its pairing is two. The
  decomposition forces `L = 0`; its identity automorphism satisfies every clause.
- Zero algebra: `HasTrivialRadical` includes it, and no `Nontrivial L` is assumed.
  Empty index sets and empty vector families are admitted.
- Rank one with an arbitrary rational rescaling: for `sl₂`, put `x = t E` with
  `t ≠ 0`. The normalization requires `θ(x) = -t⁻¹ F`; equivalently
  `θ(E) = -t⁻² F`, `θ(F) = -t² E`, `θ(H) = -H`. This is rational, involutive
  and gives `[x,-θ(x)] = H`, checking both the sign and the pinning quantifier.
- Products of simple factors: the construction works on each factor, with all
  root spaces and simple roots retained. No simplicity hypothesis was substituted.
- Root reversal is equality of submodules, not merely membership of images or one
  inclusion. Independent universes `u v` allow the algebra and finite root indices
  in arbitrary universes; no nonemptiness or universe equality is imposed.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “A split semisimple rational Lie algebra has an involutive
  Lie automorphism acting by minus one on the Cartan subalgebra and exchanging
  opposite root spaces, normalized by prescribed simple root vectors.” Eight hits:
  Geck's model Lie algebra/Cartan constructions, weight negation, root reflection
  and rank-one subalgebras. None supplies this automorphism of the prescribed algebra.
- `msearch.py`, Loogle: `LieEquiv, Function.Involutive`. Zero hits.
- `msearch.py`, Mathlib grep in `Algebra/Lie`:
  `opposition|[Cc]hevalley.*[Ii]nvol|[Ii]nvol.*[Cc]hevalley`. Zero hits.
- `msearch.py`, LeanSearch: “Chevalley opposition involution on a split semisimple
  rational Lie algebra with prescribed simple root vectors.” Eight hits concerning
  root reflections, index negation, weight negation and the Killing root system;
  none gives the requested Lie automorphism.
- `rg` in all `lean/WeilConjectures` and `lean/Sheaf`, and the upstream declaration
  index, for opposition/Chevalley-involution names: no matching theorem. Project
  hits were the Chevalley normalization consumer's proof-plan references and an
  unrelated highest-weight-dual module. The exact new declaration name is absent.
- A search for this node id in `lean/WeilConjectures` found no declaration.
  Mathlib `LieAlgebra.Basis.symm` was also read: it exchanges basis data and is not
  a Lie automorphism of the given algebra, so it is not an existing match.

No disputed statement or source correction was found. The sole compile repair was
adding `open Classical in` for the decidable equality required by the direct sum;
it does not restrict the root indexing type. Server `scompile.py` compiled both the
sandbox check and the delivered module cleanly, with no warnings (9.4 s and 1.4 s).
The node signature was extracted verbatim from the theorem through its conclusion,
excluding `:= by`; every variable and universe is explicitly bound and both
automatic-implicit options are disabled.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
