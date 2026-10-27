## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroLieDetectsFactorization` states
`AlgebraicGeometry.existsUnique_factorization_of_lie_containment_of_charZero` with one
`sorry`. There are no new definitions or other postponed theorems.

I read the node, its seven original statement dependencies, their recorded source signatures
and docstrings, and the proof dependencies' available interfaces. I read Milne's local PDF:
10.14 says that Lie preserves fibre products, Proposition 10.15 says a smooth closed subgroup
with full Lie algebra equals a connected ambient group, and Theorem 3.23 supplies Cartier
smoothness in characteristic zero. These give exactly the node's corollary, over any
characteristic-zero field, with no algebraic-closure assumption.

Hypothesis and conclusion matching:

- The field and characteristic zero are `(k : Type u) [Field k] [CharZero k]`.
- The three k-group schemes are `G H K : Over (Spec (.of k))` with `[GrpObj G]`,
  `[GrpObj H]`, `[GrpObj K]`. Bundling over the base ensures all morphisms are over k.
- Affineness of G and H is `[IsAffine G.left] [IsAffine H.left]`.
- Finite type of G and H is respectively `[LocallyOfFiniteType G.hom]`
  `[QuasiCompact G.hom]` and `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, as the
  recorded finite-type dependency specifies.
- Smoothness of G is `[Smooth G.hom]`, and connectedness is `[ConnectedSpace G.left]`.
- The closed subgroup is `(i : K ⟶ H) [IsClosedSubgroupScheme i]`. This recorded upstream
  class includes both the group-homomorphism property and the closed-immersion property.
- The homomorphism to be factored is `(f : G ⟶ H) [IsMonHom f]`.
- `GrpObj.unitSection J (IsLocalRing.closedPoint k)` is the identity point of J.
  `schemeTangentSpace k J.left J.hom` at that point is the recorded tangent-space notion.
- `hLie` quantifies over EVERY such tangent vector v of G and supplies a tangent vector w
  of K with equal differential images in H. The existing linear equivalences
  `GrpObj.lieIdentityTangentEquiv G` and `GrpObj.lieIdentityTangentEquiv K` convert these
  vectors to the canonical Lie model. Their inverses are bijective and introduce no
  extra hypothesis. `GrpObj.differential` is defined by postcomposition on dual-number
  points. Thus `hLie` is exactly df_e(Lie G) contained in the image of Lie K in Lie H.
  The canonical equivalence for H identifies the displayed equality with equality of
  tangent vectors of H. In particular this condition is equivalent to
  `(GrpObj.differential f).range ≤ (GrpObj.differential i).range`.
- `∃! g : G ⟶ K, IsMonHom g ∧ g ≫ i = f` asserts existence, compatibility with the group
  structures, the factorization equation, and uniqueness among group homomorphisms
  satisfying that equation. It asserts no uniqueness for maps failing those conditions.
- No smoothness, connectedness, normality, or commutativity of H or K is assumed. No
  separate finiteness or affineness of K is assumed; these follow from its closed immersion.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`; characteristic zero uses `CharZero`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` and its superclass `IsSubgroupScheme`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`:
  `AlgebraicGeometry.schemeTangentSpace`, with its canonical additive/module instances.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` (transitively imported):
  `AlgebraicGeometry.GrpObj.Lie` and its Lie/module structures;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential`:
  `AlgebraicGeometry.GrpObj.differential` (canonical postcomposition, not an arbitrary map).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv`:
  `AlgebraicGeometry.GrpObj.lieIdentityTangentEquiv`; its source signature and implementation
  show that it applies over any field and every group scheme, without smoothness.

I added the already landed nodes `def-wf-lie-algebra-derivation` and
`lem-ag-lie-identity-tangent-equiv` to `stmt_deps` to record the actual Lie model and the
explicit canonical bridge used in the signature. Both have usable upstream declarations.
A read-only traversal of statement and proof dependencies confirms neither addition creates
a cycle. No node statement is changed and no dependency record is changed.

The available proof dependencies are imported with plain `import`: pullbacks from Mathlib,
`Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra.affine_finiteType_algebra_of_field`, and
`WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier.smooth_of_grpObj_of_charZero`.
The closed-immersion definitions and base-change instances already come through the public
subgroup module. `lem-sfb-smooth-subgroup-full-tangent` currently has no Lean declaration;
it is a proof dependency only, so it is described in the proof docstring but cannot yet be
imported. Nothing from it is needed to type this statement.

Edge cases checked before drafting: the trivial group and zero tangent spaces are included;
K=H gives the factor f; K the identity subgroup gives the correct zero-differential criterion;
disconnected H and K are permitted. Empty groups are impossible because of the unit section.
Disconnected G would fail (a nontrivial finite constant group maps nontrivially with zero Lie
algebra); connectedness is present. In characteristic p the Frobenius of the additive group
has zero differential without factoring through the identity; characteristic zero is present.
No geometric connectedness, algebraic closedness, perfection, or normality was added. All
objects live in one arbitrary universe u as in the recorded scheme tangent-space interface;
there is no quantification over smaller test algebras that could make the condition vacuous.

Searches made using the prescribed msearch wrapper:

- LeanFinder: “A homomorphism of connected algebraic groups in characteristic zero factors
  through a closed subgroup if the differential at the identity lands in its tangent space”.
  Eight unrelated results (manifold tangent maps, abstract Lie extensions, topological groups);
  no algebraic-group factorization criterion.
- Loogle: `AlgebraicGeometry.schemeTangentMap, AlgebraicGeometry.IsClosedSubgroupScheme`.
  No hit; service does not index the project's tangent-map name.
- Mathlib grep: `(Lie|tangent).*(factor|subgroup)|differential.*subgroup`, AlgebraicGeometry.
  Zero hits.
- LeanSearch: “A connected algebraic group homomorphism in characteristic zero factors
  through a closed subgroup if its differential has image in the Lie algebra of the subgroup”.
  Eight abstract Lie-subalgebra and Lie-homomorphism results; no matching geometric theorem.
- Read-only rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, proposed declaration name, Lie containment, and differential/factorization
  patterns: no exact match. Narrow searches found the existing `GrpObj.differential`,
  `identityTangentTransport`, and `lieIdentityTangentEquiv`, which are reused. The closest
  general-linear closed-subgroup comparison is restricted to matrix presentations and
  algebraically closed fields, so is not an existing statement of this node.

Validation: scompile.py compiled the module in sandbox mode and library mode cleanly
(1.8 seconds each), with no diagnostic. Every variable and universe is explicit, with
`set_option autoImplicit false`. The only theorem proof is `by sorry`.
No STATEMENT-DISPUTED or source-statement correction is needed.

## Second reading by Q38

This is the author's separate second reading; the maintainer supplies independent review.
I reopened the node and complete module and compared every binder and clause. Field,
characteristic, the two affine finite-type hypotheses, smoothness and connectedness of G,
the closed subgroup i, and the homomorphism f match exactly. I specifically rechecked
that `IsClosedSubgroupScheme i` supplies `IsMonHom i`, so the differential is canonical
without another assumption. The quantified tangent vectors cover all of Lie G and Lie K
because the existing canonical bridges are linear equivalences; equality is in the single
canonical Lie H, so no unintroduced residue-field identification is assumed. The final
`∃!` requires the factor to be a group homomorphism and uses the correct composition order.
There is no hidden smoothness or connectedness condition on H or K. The docstring carries
all four original proof steps. No mismatch was found and no mathematical statement changed.
