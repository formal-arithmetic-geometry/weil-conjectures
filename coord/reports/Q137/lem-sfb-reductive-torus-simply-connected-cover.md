## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveTorusSimplyConnectedCover`
states `AlgebraicGeometry.reductive_torus_simplyConnected_cover`, with the sole proof
`sorry`. No definitions or subsidiary theorems are introduced. The node's natural-language
statement and proof are unchanged. Its statement dependencies gain the three already-landed
notion nodes for reductivity, semisimplicity and split tori.

Clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The field universe u is explicit; no characteristic assumption is imposed.
- The F-group scheme G is `G : Grp (Over (Spec (.of F)))`. This is the bundled form
  of the recorded `CategoryTheory.GrpObj` interface; its scheme and structure map
  are `G.X.left` and `G.X.hom`.
- Reductivity is `hG : ReductiveTorusCentralizer.IsReductive G`, the existing
  definition. Unfolding it gives affine finite type, smoothness, connectedness
  after algebraic closure and triviality of every connected normal closed smooth
  unipotent subgroup after algebraic closure. Because F is algebraically closed,
  base change to its algebraic closure is an isomorphism of fields, so these
  geometric conditions are equivalent to the node's conditions over F itself.
  `SolvableGroupStructure.IsAlgebraic` is `IsAffine`, `LocallyOfFiniteType` and
  `QuasiCompact`; the last two together are finite type. Its `IsUnipotent` includes
  smoothness and a faithful closed matrix representation, testing nilpotence of
  matrix minus identity at all geometric points, with a positive exponent.
- The integer r >= 0 is `r : ℕ`, including zero. The torus T is exactly
  `(MultiplicativeType.splitTorus F r).X`, the existing finite product of
  `StandardGroupSchemes.multiplicative F`. The latter is Spec F[t,t^-1] with the
  Laurent Hopf group law, hence represents A -> A^×, not a chosen abstract group.
- S is an existentially quantified `Grp (Over (Spec (.of F)))`.
  `IsSemisimpleGroupScheme S.X` is the recorded definition: smooth, connected,
  affine, locally finite type and quasi-compact, with every smooth connected
  solvable normal closed subgroup terminal over F. Its solvability predicate
  terminates the scheme-theoretic derived subgroup series.
- Simple connectedness is the displayed universal clause over every
  `S' : Over (Spec (.of F))` with `[GrpObj S']` and
  `IsSemisimpleGroupScheme S'`, every `f : S' ⟶ S.X` with `[IsMonHom f]`,
  `Surjective f.left`, finite `GrpObj.ker f`, and central kernel, concluding
  `IsIso f`. Centrality here is explicitly commutation of kernel points with
  all source points on every test scheme Z over F. Testing arbitrary schemes is
  equivalent to the stated testing of scalar algebras: restrict to an affine
  open cover of Z and glue the equality. The isomorphism predicate on the underlying
  over-scheme map is equivalent to a group-scheme isomorphism for a homomorphism.
- The map p is an existential morphism
  `(MultiplicativeType.splitTorus F r).X ⊗ S.X ⟶ G.X` with an existential
  `IsMonHom p` witness. Cartesian tensor in `Over (Spec (.of F))` is the actual
  fibre product over F, with its product group law.
- Faithful flatness is `p.left.appTop.hom.FaithfullyFlat`, i.e. the coordinate
  pullback equips the source coordinate ring with a faithfully flat module
  structure over the target coordinate ring. Mathlib's `RingHom.FaithfullyFlat`
  is defined through `Module.FaithfullyFlat` with precisely this ring action.
- Finite kernel is `IsFinite (GrpObj.ker p).hom`. The kernel is the pullback
  along the identity section, not the kernel on F-points. A finite scheme over
  the field is affine with finite-dimensional coordinate algebra, as required.
- Centrality is the equality `(x ≫ GrpObj.kerι p) * g = g * (x ≫ GrpObj.kerι p)`
  for every test scheme Z, kernel point x and product-group point g. It retains
  all scalar extensions, including nonreduced test algebras.
- The final injectivity clause is `Function.Injective p.left.appTop.hom`.
  No multiplicative-type conclusion or extra geometric assumption is added.
- The cases r = 0 and S = 1 are allowed: the split-torus definition's zero branch
  is the tensor unit, and the semisimple definition admits the terminal group.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; the algebraic-closure node's match
  explicitly includes IsAlgClosed, so an algebraic extension of F is not assumed.
- `CategoryTheory.GrpObj`, `Mathlib.CategoryTheory.Monoidal.Grp`, and the bundled
  `Grp` form; `IsMonHom`, `GrpObj.ker`, `GrpObj.kerι`, and the finiteness convention
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. The kernel
  declarations themselves are in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `ReductiveTorusCentralizer.IsReductive`,
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`.
- `IsSemisimpleGroupScheme` and its derived-series predicates,
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`.
- `MultiplicativeType.splitTorus`, `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`,
  reached by the public reductivity import; `StandardGroupSchemes.multiplicative`,
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- `RingHom.FaithfullyFlat`, `Mathlib.RingTheory.RingHom.FaithfullyFlat`.

The stated proof dependencies are imported without `public`: the landed
`centralTorus_semisimple_derived_product` and `multiplicativeIsogeny_comp`, and
Mathlib's geometric connectedness and faithfully flat ideal-contraction modules.
The smooth-composition Mathlib match is already publicly available through the
statement imports. The nodes reductive-radical-quotient,
semisimple-multiplicative-universal-cover and split-lattice-torus-projection have
no Lean record in the read snapshot, so there is no recorded module to import for
those proof-only prerequisites. They are not needed to type this statement.

Edge cases checked before drafting: G = 1 allows both factors trivial; a torus
allows S = 1; a semisimple group allows r = 0. The general linear-group cover can
have kernel μ_n, including nonreduced μ_p in characteristic p. Neither finiteness
nor centrality is replaced by a statement on field-valued points. No positive-rank,
nontrivial-group, characteristic-zero, kernel smoothness or separability condition
is imposed. Group-object identity sections prevent the empty scheme from being
an accidental group example. All binders and the universe are explicit under
`set_option autoImplicit false`.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: "Every connected reductive algebraic group over an
  algebraically closed field has a faithfully flat central cover by a split torus
  times a simply connected semisimple group". Eight hits concern Lie algebras,
  Galois categories and central algebras; none is this group-scheme cover.
- `msearch.py ... loogle`: `IsSemisimpleGroupScheme, IsReductive` returned zero
  hits, reporting the first identifier unknown in Mathlib.
- `msearch.py ... grep`:
  `centralIsogeny|central_isogeny|SimplyConnected.*Semisimple|ReductiveGroup`
  returned zero Mathlib hits.
- `msearch.py ... leansearch`: "A reductive algebraic group has a central cover
  by a torus times a simply connected semisimple group" returned eight hits on
  abstract centers, Lie radicals and central simple algebras; no exact match.
- `rg` on `lean/WeilConjectures` for the item id returned no occurrence. Searching
  both `lean/WeilConjectures` and `lean/Sheaf` for IsReductive, IsSemisimple,
  CentralIsogeny, and simply-connected cover names located the existing terminology
  above and specialized central-isogeny statements, not this theorem. The existing
  RhoSectionModules and SimplyConnectedCharacterLattice modules use the same
  expanded central-isogeny criterion, which was read in full.
- The upstream name index `dag/lean_names_upstream.json` has no item-id occurrence.
  DAG definition searches found the existing reductive, semisimple and torus nodes;
  they are reused, with no new definition node.

Source validation: read the local Milne PDF by `pdftotext`, including Proposition
21.60(a)--(c), Theorem 18.25, Remark 18.27 and Proposition 19.15. The last gives
exactly the central-isogeny criterion used here. There is no statement dispute,
no correction, no dependency-module repair and no new node.

Validation: `scompile.py Q137 lem-sfb-reductive-torus-simply-connected-cover` on the
module passed both its sandbox and library-module checks (1.8 s and 2.0 s), with
no compiler errors or warnings.

## Second reading by Q137

Re-read the node and final Lean signature clause by clause after compilation.
The field has both Field and IsAlgClosed, reductivity is the already recorded
predicate, r ranges over all naturals, and S carries the full semisimple predicate.
The simple-connectedness quantifier requires a semisimple source, a homomorphism,
scheme surjectivity and finite central scheme-theoretic kernel before IsIso; it
requires neither source simple connectedness nor a separable map. The covering
map is from the actual split-torus product, with a homomorphism witness and all
four required clauses (faithfully flat, finite kernel, central kernel, injective
pullback). Kernel centrality quantifies over the source of the respective map,
not its target. The rank-zero and trivial-group cases remain permitted. No
mismatch was found and no mathematical clause was changed. This is the worker's
second pass; no separate agent was started, as the dispatcher brief prohibits it.
The maintainer's independent delivery review remains the independent reading.
