## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ConnectedNormalSubgroupReductive`
states `AlgebraicGeometry.isReductive_of_smooth_connected_closed_normal_subgroup`.
Its only proof is `sorry`; no definitions or auxiliary claims are introduced.
The item's natural-language statement and dependencies are unchanged; only its
`lean` field is attached.

Source checked: Milne, Algebraic Groups (2017), Corollary 21.53, printed p.441:
every connected normal subgroup variety of a reductive group is reductive.
Section 6.46, printed p.135, gives the largest connected normal unipotent subgroup
and the geometric definition of reductivity. The node's explicit smoothness
matches the meaning of subgroup variety. The declaration docstring reproduces
the node's four-step unipotent-radical argument and names its dependencies.

Hypotheses and conclusion, clause by clause:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe is explicit and arbitrary, with `set_option autoImplicit false`.
- The two F-group schemes are `(G M : Grp (Over (Spec (.of F))))`.
  Bundled group objects supply their operations and laws without assuming
  commutativity.
- The reductive affine finite-type group G is
  `(hG : ReductiveTorusCentralizer.IsReductive G)`. The exact recorded predicate
  includes `SolvableGroupStructure.IsAlgebraic G`, hence `IsAffine G.X.left`,
  `LocallyOfFiniteType G.X.hom`, and `QuasiCompact G.X.hom`; it includes
  `Smooth G.X.hom`, connectedness after the fixed algebraic closure, and
  triviality of every smooth connected closed normal unipotent subgroup there.
  Since F is algebraically closed, geometric connectedness here agrees with
  connectedness of G. No stronger separate assumptions on G are imposed.
- The inclusion M into G is the bundled group homomorphism `(i : M ⟶ G)`.
  `[IsClosedSubgroupScheme i.hom.hom]` states it is a subgroup inclusion and a
  closed immersion; `[IsNormalSubgroupScheme i.hom.hom]` states normality of
  its image on every commutative F-algebra, including nonreduced algebras.
- Smoothness of M is `[Smooth M.X.hom]`; its connectedness is
  `[ConnectedSpace M.X.left]`. No affine or finite-type hypothesis on M is
  added: these follow from being a closed subgroup of the affine finite-type G.
- The conclusion `ReductiveTorusCentralizer.IsReductive M` is the very same
  recorded reductivity predicate used for G, so no clause of reductivity is
  weakened or replaced by a condition only on field-valued points.
- The trivial subgroup is not excluded by any positive-dimension or
  nontriviality condition. There is no `CharZero`, characteristic restriction,
  semisimplicity hypothesis, or commutativity hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with its polynomial
  splitting definition and the documented equivalent root condition;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and its bundled
  version `CategoryTheory.Grp`, specialized to `Over (Spec (.of F))` as the
  recorded group-scheme dependency instructs.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
  Read their full definitions, including injectivity and normality on all
  commutative test algebras and the underlying closed immersion field.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`; its full definition
  was read along with `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent` in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.
  Unipotence there uses a closed faithful finite-dimensional matrix
  representation and `(r(x)-1)^N = 0` for a positive N over every algebraically
  closed extension. Smoothness is part of this recorded predicate.

The statement definitions arrive through the public import of the recorded
reductivity module. Stated proof dependencies are available through that import,
the two ordinary Mathlib imports, and the ordinary import of
`Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric`, whose theorem and
full signature were read. The existing node `lem-sfb-unipotent-radical-existence`
has no Lean record yet; its proof import cannot be added until it is stated.
It is not needed to type the current statement and no duplicate is introduced.

Edge cases checked mathematically before writing: M = 1, M = G, and G = 1 all
satisfy the intended conclusion. Positive characteristic is included; smoothness
of M is explicitly retained, so infinitesimal nonsmooth subgroup schemes are
not accidentally asserted reductive. The empty scheme is excluded by
`ConnectedSpace` and the group identity. A torus is allowed as ambient group,
so semisimplicity is not accidentally assumed. The actual algebraic-closure
form of the reductivity predicate is retained for both hypothesis and conclusion.

Searches actually run:

- `msearch.py ... leanfinder "Every smooth connected closed normal subgroup of
  a reductive affine algebraic group over an algebraically closed field is
  reductive"`: eight Lie-algebra/root-system hits, no group-scheme theorem.
- `msearch.py ... loogle '"reductive"'`: zero hits.
- `msearch.py ... grep '[Rr]eductive|unipotentRadical|unipotent_radical'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "A smooth connected normal closed subgroup scheme
  of a reductive affine algebraic group is reductive"`: eight abstract or
  topological subgroup/normalization hits, no match.
- `rg -n 'connected-normal-subgroup-reductive|isReductive|IsReductive'` on
  `lean/WeilConjectures` and `lean/Sheaf`: existing reductivity definitions and
  consumers, but no theorem for smooth connected closed normal subgroups.
- `rg` for reductivity and normal subgroups in the upstream GroupScheme
  directory and the node-id `grep -rn` across upstream: no exact statement.
  The chosen full declaration name is new.

Validation: `scompile.py NS lem-sfb-connected-normal-subgroup-reductive` compiled
the delivered file in sandbox and library contexts on the server, both in 1.7 s,
with no errors or unexpected warnings. There are no disputed statements or
node corrections, no new nodes, and no dependency-module repairs.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
