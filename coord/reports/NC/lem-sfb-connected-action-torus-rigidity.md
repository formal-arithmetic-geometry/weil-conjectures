## Worker report

The module `Sheaf.AlgebraicGeometry.ConnectedActionTorusRigidity` states
`AlgebraicGeometry.connected_action_torus_rigidity`. Its only theorem has proof
`sorry`; it introduces no definitions or auxiliary claims.

I read the item, all seven original statement-dependency nodes and their recorded
interfaces, and Milne, Algebraic Groups (2017), Theorem 12.36 and Corollary 12.37,
printed pp.243--244 (including Lemma 12.35 and the torsion-density argument).
Corollary 12.37 gives precisely the asserted triviality; the node explicitly
specializes it to smooth geometrically connected groups and tori. The node's
statement and proof are unchanged.

Hypothesis and conclusion correspondence:

- The field is `{k : Type u} [Field k]`.
- The two k-group schemes, with their multiplication, inverse and identity, are
  `G T : Grp (Over (Spec (.of k)))`. This bundles exactly `GrpObj` on each
  underlying `Over` object, as the group-scheme dependency requires.
- Affineness is `[IsAffine G.X.left] [IsAffine T.X.left]`.
- Finite type of both structure maps is expressed by
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` and the corresponding
  two binders for T, following the recorded finite-type interface.
- Smoothness of G is `[Smooth G.X.hom]`.
- Geometric connectedness is `hG : ConnectedSpace
  ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left`:
  connectedness of the actual scalar extension to the algebraic closure, with
  nonemptiness included in Mathlib's `ConnectedSpace`. There is no replacement
  by connectedness of rational points.
- The torus hypothesis is `hT : MultiplicativeType.IsTorus T`. Its existing
  definition is an isomorphism of group schemes after extension to the algebraic
  closure to `splitTorus ... n`, for some `n : ℕ`. The rank-zero split torus is
  the tensor unit, so the trivial torus is included.
- The action a is `[a : ModObj G.X T.X]`. Its field `a.smul` is the morphism
  from the product over k to T. The fields `one_smul` and `mul_smul` are exactly
  the action identities. This is a genuine algebraic action, rather than an
  arbitrary family of abstract group automorphisms.
- For every commutative k-algebra `A : CommAlgCat.{u} k`, points are morphisms
  from `(algSpec (.of k)).obj (op A)`. The binder `hhom` requires
  `g • (t₁ * t₂) = (g • t₁) * (g • t₂)` for every g, t₁, t₂. Multiplication is
  the recorded group-scheme Hom-group multiplication. A multiplication-
  preserving map between groups preserves the identity and inverses. The
  inverse of the map `t ↦ g • t` is `t ↦ g⁻¹ • t` by the action laws, so this
  condition is equivalent to the stipulated group automorphism condition;
  bijectivity is not omitted as a mathematical assumption. Naturality under
  change of A follows because the action is a morphism of k-schemes (see
  `ModObj.comp_smul`), not a separately chosen function for each A.
- The conclusion is `a.smul = CartesianMonoidalCategory.snd G.X T.X`, equality
  of the actual k-scheme morphisms in the slice, exactly the first formulation
  of the node's conclusion. Evaluation gives `a(g,t)=t` on every algebra.
  The second formulation in the node is explicitly equivalent, not an
  additional independent assertion, so it is not added as a redundant conjunct.
- The blanket convention on closed subgroup schemes introduces no subgroup
  variable or subgroup assertion in this particular theorem. The existing
  subgroup-scheme module is imported, and the proof's torsion subgroups have
  the closed meaning of that module and StandardGroupSchemes.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (through the group-scheme imports).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, as recorded by
  def-sc-group-scheme. `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  supplies the recorded scheme specialization and subgroup interfaces
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and its canonical group law, used
  through the existing split-torus construction.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange`, `splitTorus`, `IsTorus`. I read their full
  definitions and added their already-landed owner node,
  `def-sfb-tori-multiplicative-type`, to stmt_deps under the rule allowing
  landed statement dependencies. This is the only non-lean field changed.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `ModObj` and its action on
  Hom groups; `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `Hom.group`.
  The Cartesian second projection is the existing product projection.

Proof imports cover the stated proof dependencies:
`Mathlib.RingTheory.Flat.Basic` for the recorded field-extension tensor
injectivity match; `Mathlib.AlgebraicGeometry.Pullbacks` for `pullbackSpecIso`
(and the Spec correspondence); `Mathlib.RingTheory.TensorProduct.Maps` for the
recorded algebra tensor-product interface. The torsion parameter and joint
injectivity nodes have no Lean records in the read repository, so there is
currently no recorded module to import for them. They are proof prerequisites,
not missing notions needed to state this theorem. StandardGroupSchemes and
connectedness are already public statement dependencies.

Edge cases checked before writing: rank zero gives the trivial torus; the
acting group may be the trivial group; no positive-rank, nontriviality,
characteristic-zero, perfect-field, or algebraically-closed-field hypothesis
is imposed. The quantifier on A includes nonreduced and zero algebras, so
positive-characteristic infinitesimal tests are retained. Geometric
connectedness is nonempty connectedness, as the node demands; empty group
schemes are excluded by their identity section anyway. Every universe and
variable is explicit with `set_option autoImplicit false`. The algebra tests
live in the same universe as the field and schemes, not an independently
smaller universe: representable morphisms are detected there, and equality of
morphisms also evaluates on larger algebra universes after the usual size
transport. There are no hollow or automatically true hypotheses substituted
for geometric assumptions.

Searches performed:

- msearch LeanFinder: “Every algebraic action by group automorphisms of a
  smooth geometrically connected algebraic group on a torus is trivial”. Eight
  hits on Galois-category connected actions, none the algebraic torus rigidity
  statement.
- msearch LeanSearch: “A connected algebraic group acts trivially by group
  automorphisms on an algebraic torus”. Eight hits including `Action.ρAut`,
  fixed-field automorphisms and categorical Galois actions; no matching
  algebraic-group theorem.
- msearch Loogle initially queried `CategoryTheory.GrpObj,
  CategoryTheory.MulAction, AlgebraicGeometry.IsTorus`: unknown identifier
  `CategoryTheory.MulAction`, so this query did not establish absence.
  A follow-up queried `CategoryTheory.ModObj, CategoryTheory.GrpObj` and
  returned zero hits.
- msearch grep `IsTorus|torus|action.*[Gg]roup|[Gg]roup.*action` in
  Mathlib/AlgebraicGeometry returned only an irrelevant elliptic-curve comment.
- `rg` in both project Lean roots for torus definitions and connected-action
  rigidity found the existing ToriMultiplicativeType module and other users of
  its IsTorus predicate, but no theorem stating this item. The upstream node-id
  grep and the upstream names-index search found no match for this item or a
  torus rigidity declaration. No duplicate definition was introduced.

Validation: scompile.py compiled this file on the server, both sandbox and
library-name checks, cleanly (2.2 s and 7.3 s respectively). No unexpected
warnings. No node statement correction or STATEMENT-DISPUTED issue is needed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
