## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ConnectedExtension` states
`AlgebraicGeometry.connectedSpace_of_connected_kernel` with proof `sorry`.
No definition, helper, new node, dependency repair, or statement correction is needed.
The node copy changes only `lean`.

The inherited BLOCKED ending concerned resplitting stage 1. The current node is split and
reviewed from Q91, has no `lean` record, and appears in `coord/queue.tsv` at stage 2.
`coord/brief-stage2.md` §0 (2026-10-22 stage handoff) explicitly says to continue stage 2
in this situation. There is no released repair note for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The two k-schemes are `G Q : Over (Spec (.of k))`, whose structure maps are
  `G.hom` and `Q.hom`. Their group structures are `[GrpObj G] [GrpObj Q]`.
- Affineness is `[IsAffine G.left] [IsAffine Q.left]`.
- Finite type means locally of finite type and quasi-compact, rendered for each
  structure map by `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` and
  `[LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]`.
- The k-homomorphism is `(p : G ⟶ Q) [IsMonHom p]`; being a morphism in `Over`
  includes compatibility with the k-structure maps.
- Faithful flatness in exactly the node's stated sense is `[Flat p.left]` together
  with `[Surjective p.left]`. The latter class is surjectivity of the underlying
  map on all scheme points, not only rational points.
- The specified scheme-theoretic kernel L is `(GrpObj.ker p).left`.
  In `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, `GrpObj.ker`
  is literally `pullback p η[Q]` in `Over`. The forgetful functor preserves this
  pullback; the terminal k-scheme has underlying scheme Spec k, and its unit map
  is the identity section e_Q. This is the node's fibre product, not a kernel
  of rational-point groups or a reduced subgroup.
- Connectedness of L and Q is `[ConnectedSpace (GrpObj.ker p).left]` and
  `[ConnectedSpace Q.left]`; the conclusion is `ConnectedSpace G.left`.
- No smoothness, reducedness, commutativity, separability, or characteristic
  restriction occurs in the binders. There are no additional conclusion clauses.

Dependency interfaces read and used:

- `def-weil-field`: `Field` from `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: the `IsAlgClosed` specialization described by the
  node's mathlib_match, from `Mathlib.FieldTheory.IsAlgClosed.Basic`. No choice of
  an algebraic closure or an extra base-field extension is required.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  via `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, whose module docstring
  explicitly prescribes this Over-category encoding. Its imported
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` defines `GrpObj.ker`.
  Read the full kernel definition and `GrpObj.isPullback_kerι` as well.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` from
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, whose docstring records its stalkwise
  equivalence. This same module contains the proof dependency `Flat.SpecMap_iff`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, used through the
  existing kernel construction, with projections and universal property read.
- `def-weil-connected-scheme`: `ConnectedSpace` from
  `Mathlib.Topology.Connected.Basic`, which includes nonemptiness.
- `AlgebraicGeometry.Surjective`, from
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, is already exposed by the imports.

Proof dependencies: the two new stage-1 statements
`lem-sfb-finite-constant-component-quotient` and
`lem-sfb-faithfully-flat-group-quotient-universal` have neither a Lean record nor a
Mathlib match, so there is no statement module to import for them. They are proof-only
prerequisites and need not be stated to state this theorem. The remaining proof
interfaces are imported through the public statement imports or the plain proof import
`Mathlib.RingTheory.RingHom.FaithfullyFlat`. The theorem docstring records all four
steps of the accepted proof, including scheme-level triviality on the kernel and quotient.

Source checked: `pdftotext -f 126 -l 127 literature/milne-algebraic-groups_iAG2017.pdf -`
shows Proposition 5.59(a), printed p.114, and its component-quotient proof, agreeing
with the node. No source-based correction is needed.

Edge cases checked mathematically before writing:

- The trivial group and identity homomorphism satisfy the statement; the kernel is
  the trivial k-group scheme and is connected and nonempty.
- A quotient to the trivial group has kernel G, so the hypothesis already asserts
  the required connectedness. This case is permitted.
- The empty scheme cannot have a k-group identity section, and `ConnectedSpace`
  excludes empty kernels and quotients as the node requires.
- Frobenius on the additive group in characteristic p, with nonreduced connected
  kernel alpha_p, is covered. No smoothness of the kernel is assumed.
- Without connectedness of the kernel, a nontrivial finite constant group mapping
  to the trivial group gives a disconnected source. Without connectedness of Q,
  its identity morphism gives the corresponding example. Both assumptions matter.
- Characteristic zero and every positive characteristic are permitted. The arbitrary
  universe u is explicit; there are no implicit or auto-bound universe parameters.

Searches for existing statements and notions:

- `msearch.py ... leanfinder` query: "A faithfully flat homomorphism of finite type
  affine group schemes over an algebraically closed field with connected scheme
  theoretic kernel and connected quotient has connected source". Eight hits: six
  categorical Galois connectedness results, the affine faithful-flatness criterion,
  and `AlgebraicGeometry.Flat`; none states this group-scheme extension theorem.
- `msearch.py ... loogle` query: `"ConnectedSpace", "ker"`. Zero hits.
- `msearch.py ... grep` query:
  `(connected|preconnected).*(kernel|exact)|(kernel|exact).*(connected|preconnected)`
  in `AlgebraicGeometry`. Three hits in `Geometrically/Connected` and
  `Sites/ConstantSheaf`; none is this statement.
- `msearch.py ... leansearch` query: "An extension of connected affine algebraic
  group schemes by a connected scheme theoretic kernel is connected". Eight hits
  about abstract GroupExtension and AddGroupExtension; none concerns scheme topology.
- `rg` of the same connected/kernel/extension patterns in project `lean/WeilConjectures`
  and `lean/Sheaf` found no matching extension theorem. More focused inspection of
  `GroupScheme` confirms existing kernels, finite connected group orders, central
  isogenies, and a stronger smooth affine-normal-quotient geometry result, none of
  which states this theorem for arbitrary nonreduced connected kernels.
- Searching the item id in `lean/WeilConjectures` found no attachment. Searching
  `GrpObj.ker` and `IsMonHom` found the reusable existing kernel and group interfaces;
  these are used without private copies.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q25

Author's second reading (no other agent was started): reopened the node and delivered
module. The field, algebraic-closedness, affine group structures, both finite-type
conditions, k-homomorphism, flatness, topological surjectivity, scheme-theoretic kernel,
and both connectedness assumptions are all present exactly as listed above. The only
conclusion is connectedness of the underlying space of G. In particular the kernel is
`GrpObj.ker p`, not its reduced subscheme or its k-points; no smoothness or commutativity
was slipped in. The universe and every binder are explicit, with autoImplicit disabled.
The proof docstring retains the four steps of the accepted split. No mismatch or
statement change was found. Independent review is supplied by the maintainer as
specified in the dispatch brief.

Validation: `scompile.py Q25 lem-sfb-connected-group-extension` compiled the delivered
file in sandbox mode (1.6 s) and its actual library module (1.5 s), exit code 0,
with no errors or unexpected warnings. Every Lean line is at most 100 characters.
