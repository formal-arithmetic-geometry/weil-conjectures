## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGroupRationalPointSubspaceTest` states
`AlgebraicGeometry.GeneralLinearGroup.map_subspace_eq_iff_forall_algebra`, with one `sorry`
and no new definitions. The node is unchanged except for its `lean` field. There are no
new nodes, dependency repairs, statement corrections or disputed statements.

Source checked directly: Milne, Algebraic Groups, iAG2017 PDF, printed p.85, Proposition 4.3
and Corollaries 4.4--4.5 (PDF page 97); printed pp.9--10, Proposition 1.10 and its following
base-extension statements (PDF pages 21--22). The source's stabilizer is the all-algebra
subspace-preservation functor. Smoothness and the Nullstellensatz supply its required
schematic density here. This item is a supporting lemma, not a blueprint unit statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- A group scheme over k is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  Affineness is `[IsAffine G.left]` and smoothness is `[Smooth G.hom]`.
- Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the conjunction
  specified by the finite-type dependency's record.
- The arbitrary finite-dimensional vector space is `{V : Type v} [AddCommGroup V]
  [Module k V] [FiniteDimensional k V]`. Its universe v is independent of u.
- The permitted basis choice is `b : Module.Basis m k V`, with `m : Type u`,
  `[Fintype m] [DecidableEq m]`. Every finite-dimensional V admits such an index and
  basis (use a finite ordinal lifted to u). There is no nonemptiness assumption on m.
- The rational representation is the actual k-scheme morphism
  `ρ : G ⟶ GeneralLinearGroup m k`, with `[IsMonHom ρ]` expressing its group law.
  No arbitrary family of point actions or additional compatibility hypothesis is used.
  `homMulEquiv m k A (g ≫ ρ)` is exactly its canonical matrix on A-points.
- The arbitrary k-linear subspace is `W : Submodule k V`.
- Condition (i) is `∀ g : AlgebraicGeometry.points G k,
  W.map (Matrix.toLin b b (homMulEquiv m k k (g ≫ ρ))) = W`.
  `Matrix.toLin b b` uses the chosen basis to act on the original V.
- The equivalence is the literal `↔` between (i) and (ii).
- Condition (ii) quantifies over `∀ (A : Type u) [CommRing A] [Algebra k A]`
  and `g : AlgebraicGeometry.points G A`. Algebras share the scheme/base universe,
  as in the existing group-scheme and GL functor-of-points interfaces. In particular
  there is no independent smaller algebra universe and no missing A=k test.
- `W.baseChange A` is Mathlib's range of the base-changed inclusion
  `W.subtype.baseChange A`, a submodule of `A ⊗[k] V`. The inclusion is injective since
  W is a subspace over a field and its inclusion splits. Tensor symmetry identifies
  this submodule with the node's `W ⊗[k] A` inside `V ⊗[k] A`.
- `b.baseChange A` has vectors `1 ⊗ b i`, so
  `Matrix.toLin (b.baseChange A) (b.baseChange A)` of the evaluated matrix is precisely
  the induced A-linear action on that scalar extension. Mapping `W.baseChange A` and
  equating it to itself states equality of submodules, not just containment.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The algebraic-closure dependency's match
  explicitly identifies `IsAlgClosed` as its algebraically closed-field clause.
- `CategoryTheory.GrpObj`, `Mathlib.CategoryTheory.Monoidal.Grp`, and
  `CategoryTheory.IsMonHom`, together with the group-scheme interpretation documented
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `FiniteDimensional`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is imported as recorded for
  `def-sc-general-linear-group`. Its docstring and node expressly reuse the upstream
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`; these are the GL
  component needed here. The SL construction is not substituted for GL.
- `AlgebraicGeometry.points`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`: the actual abbreviation
  for morphisms `Spec A ⟶ G` over `Spec k`.
- `Module.Basis.baseChange`, `Mathlib.LinearAlgebra.TensorProduct.Basis`;
  `Submodule.baseChange`, `Mathlib.LinearAlgebra.TensorProduct.Tower`;
  `Matrix.toLin`, `Mathlib.LinearAlgebra.Matrix.ToLin`.
- Proof dependencies are plain imports:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`, containing
  `AlgebraicGeometry.Smooth.geometricallyReduced`, and
  `WeilConjectures.Mathlib.RingTheory.Nullstellensatz`, containing
  `eq_zero_of_forall_algHom_apply_eq_zero` (plus the other two clauses).
  `AlgebraicGeometry.IsReduced` in `Mathlib.AlgebraicGeometry.Properties`, the recorded
  reduced-scheme definition, is already exposed by the smooth-morphism dependency.

Edge cases checked before writing:

- V=0: m can be empty; the upstream GL construction works for the empty index,
  whose determinant is 1. Its matrices form the trivial group. The unique W is zero,
  and both image equalities hold.
- W=0 and W=V: base change gives bottom and top respectively. Every evaluated matrix
  is invertible, so it preserves both, including when V is zero.
- A=0 is permitted by `[CommRing A]` without `[Nontrivial A]`; scalar extension is zero.
- Positive characteristic and disconnected smooth groups are included: no characteristic
  zero, connectedness, irreducibility or faithfulness assumption is imposed.
- Smoothness matters: for alpha_p in characteristic p, the rational points are trivial,
  while its upper-unipotent two-dimensional representation over k[t]/(t^p) moves the
  line spanned by the second coordinate vector. This excluded counterexample confirms
  the density argument needs reducedness rather than topological density alone.

Searches for existing declarations:

- `msearch.py ... leanfinder`: "A subspace of a rational representation of a smooth affine
  group over an algebraically closed field is stable if every rational point preserves it".
  Eight hits, including `Algebra.isInvariant_iff`, `Algebra.IsInvariant.isInvariant` and
  affine-space pointwise action lemmas. None states this all-algebra equivalence.
- `msearch.py ... loogle`: "Submodule.stabilizer, Representation". Zero hits;
  Loogle reports unknown identifier `Submodule.stabilizer`.
- `msearch.py ... leansearch`: "Rational points of a smooth affine algebraic group detect
  invariant subspaces over all algebras". Eight hits on abstract representations and
  invariant algebras, including `Representation.invariants`; no scheme-theoretic test.
- `msearch.py ... grep`: "stable.*subspace|subspace.*stable|schematicallyDense|
  schematically_dense" in `AlgebraicGeometry`: zero Mathlib hits.
- `rg` on the project's `lean/WeilConjectures` and `lean/Sheaf`: read the GL,
  RationalHom, Representation, Lie, and DenseRestrictionSemisimple modules. The Lie
  stability results concern dual numbers or characteristic zero and connected groups,
  not all test algebras here. The simple/semisimple abbreviations also impose
  characteristic zero. `DenseRestrictionSemisimple` cites this node as a proof input,
  and does not state the equivalence. Searching the exact node id in WeilConjectures
  and the proposed theorem name in both roots and `dag/lean_names_upstream.json`
  finds no existing declaration.

Validation: `scompile.py Q32 lem-sfb-smooth-group-rational-point-subspace-test <module>`
compiled both the sandbox and the library-name file cleanly, each in 1.7 seconds.
The first attempt identified the missing import exposing `AlgebraicGeometry.points`;
adding its defining public module fixed that error. Every universe and variable is
explicitly bound, with `set_option autoImplicit false`. The only postponed proof is
this node's named theorem, with the complete five-step proof in its docstring.

## Second reading by Q32

This is a second pass by the same worker, not an independent-agent review: the dispatcher
explicitly forbids starting other agents and assigns independent review to the maintainer.
Reopened the node and finished file and checked all the correspondences above. In particular:
finite type includes quasi-compactness; the basis is allowed to be empty; the representation
is a group homomorphism of k-schemes; every A-point comes from the same scheme morphism;
the RHS is an A-submodule image equality; no smoothness, field-closure, or finite-dimension
hypothesis is dropped. The tensor ordering changes only by the canonical symmetry, and
`b.baseChange` explicitly supplies the transported action. No statement change was needed.
