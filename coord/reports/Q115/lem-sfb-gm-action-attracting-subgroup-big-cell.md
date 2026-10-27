## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GmAttractingBigCell` states
`AlgebraicGeometry.GmAttractingBigCell.exists_attracting_subgroups_bigCell` with a single
`sorry`. The four preceding definitions supply explicit coordinate substitutions and predicates
belonging to this statement; none selects data from an existence theorem. No theorem is proved.

Hypothesis and clause correspondence, reading the node and Lean together:

- Any field k: explicitly bound `{k : Type u} [Field k]`; no algebraic closure, infinitude,
  characteristic, or perfectness assumption.
- H a k-group scheme: `H : Grp (Over (Spec (.of k)))`, the recorded internal group notion.
- Affine, smooth, geometrically connected, finite type: `[IsAffine H.X.left]`,
  `[Smooth H.X.hom]`, `[GeometricallyConnected H.X.hom]`, and the two finite-type
  instances `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- The morphism a with identity and associativity: the instance
  `[a : ModObj (StandardGroupSchemes.multiplicative k) H.X]`, whose `smul`, `one_smul`,
  and `mul_smul` are exactly those maps and diagrams. Preservation of multiplication is
  `hAut : TorusCharacterTangent.ActsByGroupAutomorphisms ... H`. Testing all schemes is
  equivalent to the all-algebra identities since affine schemes cover every test scheme.
- For every commutative k-algebra R, `points H.X R` is the existing functor of points.
  `IsAttracting H sign R h` asks for `f : points H.X (Polynomial R)` whose restriction
  by `Polynomial.toLaurentAlg` is the given orbit at the universal Laurent unit and
  whose evaluation at zero is 1. This is precisely an R-morphism A1_R -> H_R, using
  the standard base-change adjunction. `sign = 1` gives Uplus, `sign = -1` gives Uminus.
  `gmPoint` is the Laurent algebra universal map induced by the actual chosen unit;
  no arbitrary orbit or scalar-extension map is introduced.
- Representation by closed subgroups: existential `Uminus Uplus : Grp ...` and
  homomorphisms `iminus iplus`; both `IsClosedSubgroupScheme` clauses and both
  all-algebra membership iff clauses identify their represented subfunctors exactly.
  These formulas are natural because all maps are compositions of actual scheme maps.
- Both subgroups are smooth and geometrically connected: the four displayed property
  clauses. Affineness follows from their closed inclusions in affine H; it is not an
  additional requested assertion or hypothesis.
- Stability: existential internal restricted actions `aminus`, `aplus`, and the two
  equations `lift s x ... = s • (x ≫ i)` for every test scheme. Their inclusions therefore
  commute as actual scheme morphisms with a. For a closed inclusion stability uniquely
  induces this action by Yoneda, so this is equivalent to the node's stability assertion.
- Identity tangent module h: existing `GrpObj.Lie H.X`, its canonical dual-number point
  `GrpObj.tangentPoint`, and the existing linear differential `GrpObj.differential`.
  This is the identity tangent model canonically identified with `schemeTangentSpace` by
  upstream `GrpObj.lieIdentityTangentEquiv`; no second tangent space is defined.
- Integer algebraic character space h_j: `weightSpace H j` tests each R and each unit z,
  after the actual coefficient map k[epsilon] -> R[epsilon], against substitution
  epsilon -> z^j epsilon. This expresses a(z)v = z^j v after every algebra extension.
  The displayed span bundles a set already closed under linear operations, since the
  action is by group automorphisms. It is not the rational-point-only weight predicate
  from `TorusCharacterTangent.weightSpace`, which would be unsuitable over finite fields.
- Lie(Uminus) and Lie(Uplus) inside h: the two ranges of the actual inclusion differentials
  equal `⨆ j < 0, weightSpace H j` and `⨆ j > 0, weightSpace H j`. These suprema express
  exactly the subspaces underlying the sums of the distinct integer character spaces;
  character independence makes these the indicated direct sums. No external abstract
  isomorphism replaces the inclusion maps. Equivariance is supplied by the preceding
  equations of actual action morphisms, which induce the commuting differential diagrams.
- If h_0 = 0: implication with antecedent `weightSpace H 0 = ⊥`.
- Multiplication Uminus x Uplus -> H: `multiplication iminus iplus` multiplies the
  two projected inclusion morphisms in the internal group. Its `.left` is the actual
  underlying scheme map. The conclusion is `IsOpenImmersion ... ∧ DenseRange ...`.
  DenseRange means topological density of the image, as requested.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; and Mathlib's internal action
  `ModObj` in `Mathlib.CategoryTheory.Monoidal.Mod`, with its Cartesian point action.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`,
  `IsSubgroupScheme`, and `IsMonHom` compatibility.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`, whose
  field-base-change connected-space condition renders geometric connectedness.
  `ConnectedSpace` is the recorded connectedness leaf; the geometric version retains it
  after every field extension, rather than assuming only ordinary connectedness.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `multiplicativeGroup`,
  and `map`; the multiplicative group is the recorded Spec of the Laurent Hopf algebra.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace` and its
  module structure; its identity model is the existing `GrpObj.Lie`, `tangentPoint`,
  and `differential` in upstream GroupScheme.Lie.Ring and .Differential.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `TorusCharacterTangent.ActsByGroupAutomorphisms`; its already landed owning definition
  node is added to stmt_deps. The restricted rational-point weight definition is not reused.
- `Mathlib.Algebra.DualNumber`: `DualNumber.lift`, applied to the actual coefficient map
  and epsilon, with its existing square-zero and commutation proofs. This is exactly
  k[epsilon] -> R[epsilon]. The proof dependency
  `Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus` is imported without public;
  its server source was read using `scompile.py --source`.

Proof imports: Mathlib.RingTheory.FinitePresentation contains
`Algebra.FinitePresentation.of_finiteType`; upstream Regular contains
`IsRegular.of_smooth` and `IsRegular.isIntegral`; Mathlib.AlgebraicGeometry.Properties contains
`IsIntegral`. The affine dual-number calculus and open-immersion dependencies are already
imports. `lem-sfb-relative-dynamic-subgroups` and
`lem-sfb-positive-weight-affine-space-arbitrary-field` have no recorded Lean module at the time
of this delivery, so no import can yet be added for them. They are only proof prerequisites,
not missing notions required by the present statement; their mathematical content is not
assumed or silently added to this theorem.

Source read: local Milne PDF, printed pp.263--266 (PDF pages 275--278), especially
13.29, 13.30, and 13.33(a)--(e), including the dual-number calculation and the open product.
The statement is an extracted automorphism-action version via the semidirect product, as its
existing source record explains. It is not the unit's own statement (`blueprint.is` is null).
No statement correction and no new definition nodes were necessary.

Edge cases checked before writing:

- H = 1 gives two trivial subgroup schemes, zero Lie spaces, and identity multiplication.
- A trivial action on positive-dimensional H gives Uplus = Uminus = 1; the zero-weight
  antecedent fails, so no open-point assertion is made.
- Additive groups with strictly positive or negative character weights give the appropriate
  whole or trivial subgroup, fixing the sign convention.
- Over finite fields, nontrivial characters can agree on k-points; testing all R and the
  universal Laurent unit distinguishes them. In characteristic p a character t^p retains
  weight p even though its differentiated character may vanish.
- The zero ring and nonreduced test rings are permitted throughout. The polynomial-to-Laurent
  restriction and dual-number substitutions remain the actual ring maps in these cases.
- Test rings, Laurent/polynomial rings and dual numbers all live in the base universe u;
  no independent smaller test universe makes a universal condition vacuous.

Searches made (Q115 launcher msearch logs, 2026-10-24):

- leanfinder: "Attracting subgroups of a smooth connected affine group for multiplicative
  group automorphisms are smooth connected and form an open dense big cell when tangent
  has no fixed vectors". Eight hits concerned topological groups or dynamical open sets;
  no algebraic-group attracting-subgroup result.
- loogle: `"GrpObj", "IsOpenImmersion"`: zero hits.
- grep: `attracting.*subgroup|dynamic.*subgroup|cocharacter`: zero Mathlib hits.
- leansearch: "Positive negative attracting subgroups of multiplicative group action smooth
  affine algebraic group open immersion": eight abstract subgroup/topological-group hits,
  no matching statement.
- rg on lean/WeilConjectures and lean/Sheaf: attracting/contracting/dynamic/GmAction,
  GroupScheme, tangentPoint, and weightSpace. Existing TorusCharacterTangent and
  GmRepresentation APIs were read; neither states this theorem or gives its universally
  tested differentiated action weight space. `grep -rn` for the item id in
  lean/WeilConjectures returned no hit. The general group, point, tangent, and scalar
  constructions found are reused.

No STATEMENT-DISPUTED issue. The example CompactObject module is currently withdrawn and
has no declarations; its recorded node/example layout and the current landed statement
modules were consulted for conventions. All writes remain in the assigned sandbox.

## Second reading by Q115

A second pass by the same worker (the dispatcher explicitly prohibits spawning agents)
read the full node, the source excerpt and the final file together. An independent maintainer
review is required by this worker's brief and is not claimed here. The comparison above checks
every hypothesis and conclusion. The main traps checked were the signs of the orbit, the
value-zero identity condition, geometric rather than ordinary connectedness, algebraic rather
than differentiated or rational-point character weights, and topological rather than
rational-point density. All are rendered explicitly. Actual restricted action maps express
stability and make the tangent inclusions equivariant; no existential abstract linear
isomorphism or arbitrary map replaces a canonical map. The first compiler pass found a
wrong unit-coercion homomorphism name, one ambiguous coefficient map, and one extra bracket;
these were repaired. The next pass found only an overlong line, now wrapped. Preflight
required the recorded signature without the trailing assignment token; this is repaired.
The coefficient map now uses Mathlib DualNumber.lift directly, avoiding a statement
dependency on a theorem node for an elementary map.
