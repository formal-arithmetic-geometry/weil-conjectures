## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleCentralizerMaximalTori` states
`AlgebraicGeometry.GrpObj.semisimpleCentralizer_maximalTori`, with its entire proof `sorry`.
The companion definition module `Sheaf.AlgebraicGeometry.GroupScheme.LieCentralizer` defines
`AlgebraicGeometry.GrpObj.IsLieCentralizer` by an explicit proposition. It constructs no
scheme or action by choosing from an unproved existence assertion.

Source read: Milne, Algebraic Groups (2017), Proposition 17.90 and its proof, printed p.381
(PDF page 393). It asserts exactly the stated maximality. The zero case is immediate even
though the source proof initially mentions nontrivial tori. Proposition 17.76, printed p.377,
supplies the stabilizer description. No change to the item's natural-language statement,
proof or proof dependencies was needed.

Hypothesis and conclusion correspondence:

- Field k: `{k : Type u} [Field k]`.
- Affine finite-type k-group schemes: `Grp (Over (Spec (.of k)))`, with
  `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, and the
  corresponding three conditions on C. These implement the standing convention on all
  groups. T's being a torus is part of the existing maximal-torus predicate.
- G smooth: `[Smooth G.X.hom]`.
- G geometrically connected: `[GeometricallyConnected G.X.hom]`, the standard geometric
  connectedness predicate; over a field this is connectedness after algebraic closure.
- The faithful closed linear representation is `i : G.X ⟶ GeneralLinearGroup
  (ULift.{u} (Fin n)) k`, `[IsMonHom i] [IsClosedImmersion i.left]`. A closed immersion
  supplies faithfulness on every test algebra. ULift changes only the index universe,
  allowing every finite dimension over an arbitrary Type-u field.
- The tangent vector is `X : GrpObj.Lie G.X`, the canonical relative tangent at identity.
  Its differential in the faithful representation is the existing
  `GeneralLinearGroup.RationalHom.differential i X`, identified with a matrix by
  `GeneralLinearGroup.lieAlgebraEquivMatrix`. No independent Lie algebra or differential
  is hypothesized. `GrpObj.lieIdentityTangentEquiv` identifies this model with the
  dependency's recorded `schemeTangentSpace`; the existing Lie model and canonical
  dual-number point are used directly, without an extra chosen transport.
- Geometric semisimplicity is `hX`: an invertible matrix P over `AlgebraicClosure k` and
  a diagonal d such that `P⁻¹ * (di(X)).map (algebraMap k _) * P = Matrix.diagonal d`.
  This is diagonalizability, with no separability, characteristic-zero, or perfectness
  assumption. The node's explanatory definition of noncentrality is not a hypothesis
  and is consequently not imposed.
- `C` and `j : C ⟶ G`, with `hC : IsLieCentralizer j X`, name a representing closed
  subgroup of the exact stabilizer functor. Its every R-point image is specified by
  the canonical infinitesimal-point commutation equation. The defining conjugation
  identity in `AffineGroupDualNumberCalculus.Data.conjugation` makes this equivalent
  to `Ad(g)(1 tensor X) = 1 tensor X`. All commutative test algebras are quantified;
  the algebra universe is the same u as k, never an independently smaller universe.
  This is a presentation of the stipulated object C_G(X), not an arbitrary subgroup
  assumed to satisfy the desired conclusion. Such presentations are unique over G
  by affine Yoneda; representability is the existing unstated proof dependency
  lem-sfb-semisimple-tangent-stabilizer, and is not substituted with an arbitrary choice.
- K is exactly `Grp.mk (GrpObj.identityComponent C.X)`, using the existing open
  connected-component scheme structure and its inherited group law.
- A maximal torus of K is `t : T ⟶ Grp.mk (identityComponent C.X)` with
  `hT : ReductiveTorusCentralizer.IsMaximalTorus t`.
- The conclusion is the same existing maximal-torus predicate on the composite
  `t ≫ ⟨⟨identityComponentι C.X⟩⟩ ≫ j`, hence maximality in G of the identical torus
  with its canonical composite inclusion. The predicate includes closedness, torus
  structure, and that every containing torus inclusion induces an isomorphism.

Dependency declarations read and reused:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group-object morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme` and their test-algebra/closed-immersion signatures.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Smooth`,
  `.ClosedImmersion`: `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, `IsClosedImmersion`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `baseChange`, `splitTorus`, `IsTorus`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative` and its actual
  multiplicative group law, used through the torus definition.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace` and
  `schemeTangentMap`; `GroupScheme.LieIdentityTangentEquiv` supplies the canonical
  bridge from the Lie model used here.
- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra` and commutator bracket;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` and `.Lie.Ring`:
  `GrpObj.Lie`, `lieEquivTangent`, the canonical bracket, and `tangentPoint`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`:
  `GeneralLinearGroup.RationalHom.differential` and `lieAlgebraEquivMatrix`.
  These use the existing `GeneralLinearGroup`, also used by the recorded dependency
  `Sheaf.AlgebraicGeometry.LinearGroupSchemes`. No GL construction is duplicated.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.identityComponent`,
  `identityComponentι`, the inherited group-object and homomorphism instances. The
  item's stmt_deps gains the already recorded owning node def-wf-algebraic-components.
- `Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus`: `dualMap`, `Data`'s canonical
  normalization and conjugation specification, `exists_compatible_calculus`.
  The definition uses its concrete `dualMap` and the actual `tangentPoint`, without
  selecting any Data or Ad from the theorem.

Proof-only imports retained for the already recorded proof dependencies:
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (lem-pc-proper-base-change),
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(lem-sbc-connected-rational-point-geometrically-connected), and
`Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus`.
The dual-number-calculus proof dependency is already a public dependency via the helper.
The smooth-restriction and open-factorization Mathlib APIs are exposed transitively by
statement imports. The remaining proof dependencies have neither a Lean record nor
Mathlib match in the live node files read; no unavailable module is invented or imported.
These proof dependencies are not needed to type the statement and remain for stage 3.

Edge cases checked mathematically before writing:

- X=0: the tangent point is the identity, so every g commutes with it; C=G over G,
  K=G since G is geometrically connected, and the conclusion is the original maximality.
- Central semisimple X: no noncentrality or X!=0 condition appears.
- Rank-zero torus: `IsTorus` allows the empty product, and `IsMaximalTorus` is unchanged.
- Zero-dimensional faithful representation, when permitted by the standing GL API:
  the index is empty, the diagonalization equation is meaningful; only a trivial G
  admits the stipulated closed immersion. No spurious nonempty-basis requirement.
- Nonreductive smooth groups, imperfect fields, and positive characteristic: none is
  excluded by the signature. No characteristic-zero matrix-Lie theorem is assumed.
- Nonreduced test algebras and the zero algebra are included. Commutation is tested
  in G(R[epsilon]), not merely on geometric points or on the Lie bracket.
- Every group has an identity, so the empty scheme is not accidentally admitted as
  a group scheme. No empty-space connectedness convention is changed.

Searches performed (full service responses retained in sandbox searches.jsonl and the
new node's mathlib_searches): LeanFinder for maximal tori of a semisimple Lie centralizer
returned abstract Cartan-subalgebra lemmas; Loogle `"IsSemisimple", "centralizer"` returned
zero; Mathlib grep `maximal.?torus|semisimple.*centralizer|centralizer.*semisimple` under
AlgebraicGeometry returned zero. LeanSearch `maximal torus semisimple Lie centralizer
algebraic group` returned abstract Lie semisimplicity and subalgebra centralizers.
For the helper, LeanFinder's dual-number centralizer query returned Engel/abstract Lie
lemmas, LeanSearch returned subgroup/ring centralizers, Loogle `"tangentPoint",
"centralizer"` returned zero, and Mathlib grep returned three unrelated C-star multiplier
hits. Project-wide rg found no IsLieCentralizer; the existing torus semisimple-point
centralizer concerns group elements, not tangent vectors. DAG grep found the unstated
representability theorem but no definition node; `blueprint_refs.py search 'Lie centralizer'`
returned zero. These results justify one new definition and no theorem duplication.

Validation: both delivered modules compiled separately in dependency order through
scompile.py against the current published server build. Only the theorem has sorry.
The local compile attempt reported OSError(28), no space left; the wrapper automatically
fell back to server confirmation, which compiled each module cleanly in under 3 seconds.
No source checkout writes or direct git commands were used.

No STATEMENT-DISPUTED flag, statement correction, or unusable dependency record.

## New nodes

`def-sfb-lie-centralizer` defines the predicate that a specified closed subgroup represents
C_G(X), by equality of its all-test-algebras point image with the canonical tangent-point
commutant. Source: Milne 17.76, p.377, and 10.19, pp.191–192. Its definition has real logical
data, no sorry, arbitrary action, or arbitrary object choice. It is needed to name the
centralizer in the item without assuming a new unspecified action. Existing records define
abstract centralizers or torus centralizers, and the genuine unstated
lem-sfb-semisimple-tangent-stabilizer proves existence/smoothness rather than owning this
predicate. The searches above and in mathlib_searches found no duplicate definition.
`blueprint_refs.py ancestor` returned None for the item, preserved as null in the new
node's blueprint.from.node; its via begins with the item and continues the existing chain.

## Second reading by Q98

Worker's second pass, not an independent agent reading: the dispatcher explicitly forbids
starting other agents and assigns the independent reading to the maintainer. Reopened the
node and both final modules. Checked the concrete differential and algebraic-closure
conjugation equation, all-algebra centralizer equivalence, existing open identity component,
and maximality of the same composite torus inclusion. The initial compile found the
bundled group morphism needed two constructor layers and the final GL coercion required
an explicit matrix type; both were repaired without changing the mathematical signature.
Checked no nonzero/noncentral, reductive, perfect, or characteristic hypothesis was added.
The new predicate is fully expanded and the node records reproduce the final signatures.
Independent maintainer review remains pending.
