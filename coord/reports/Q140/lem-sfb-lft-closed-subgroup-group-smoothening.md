## Worker report

The module `Sheaf.AlgebraicGeometry.LftClosedSubgroupGroupSmoothening` states
`AlgebraicGeometry.lft_closed_subgroup_group_smoothening`. Its only proof is `sorry`.
It introduces no definitions and changes only the assigned node's `lean` record.

The node and source were read, including BLR 7.1 Theorem 5 and its preceding
smooth-test-scheme universal property (printed pp.174-175), and 10.1 Proposition 4
proof (printed p.291). The primary-source PDF text was accessed at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The PDF screenshot service returned a cache-miss error; the text extraction supplied
the cited pages. The latter proof controls the smoothening on the finite type
intersection with the ambient identity component. No Neron mapping property is
used as a hypothesis here.

Hypothesis and conclusion correspondence:

- `D : Type u`, `[CommRing D]`, `[IsDedekindDomain D]`, and
  `hdim : ringKrullDim D = 1` express precisely the node's Noetherian integrally
  closed domain of dimension one. Mathlib's Dedekind class alone allows dimension
  zero, so the explicit dimension equality is necessary for this node's convention.
- `E : Type u`, `[Field E]`, `[Algebra D E]`, `[IsFractionRing D E]` give the
  fraction field; the base is literally `Spec (.of D)` throughout.
- `M : Grp (Over (Spec (.of D)))` supplies multiplication, identity, inverse and
  the group diagrams. `[IsCommMonObj M.X]` is commutativity. `[Smooth M.X.hom]`,
  `[IsSeparated M.X.hom]`, `[LocallyOfFiniteType M.X.hom]` give all three
  structural hypotheses on the ambient group. `IsSeparated` is defined by its
  closed diagonal, exactly as the node specifies.
- `M0 : Grp (Over (Spec (.of D)))`, `i0 : M0 ⟶ M`, and
  `[IsOpenImmersion i0.hom.hom.left]` exhibit an open subgroup. A morphism in
  `Grp` is a group homomorphism. Its finite type hypothesis is the pair
  `[LocallyOfFiniteType M0.X.hom]`, `[QuasiCompact M0.X.hom]`.
- `hM0` requires that, after base change along every algebraically closed field
  point `s`, the image of `i0` is exactly
  `connectedComponent (GrpObj.onePoint ((Over.pullback s).mapGrp.obj M).X)`.
  Thus it is exactly the union of fibre identity components, not an arbitrary
  open subgroup. Images of open immersions specify their open subscheme uniquely.
  Quantifying over algebraically closed field points is equivalent to checking
  the chosen algebraic closures of residue fields: connected components of
  these smooth, geometrically reduced group fibres are unchanged by further
  algebraically closed field extension. All test fields live in the same
  universe as the base, avoiding a vacuous smaller-universe test.
- `C : Grp (Over (Spec (.of D)))`, `[IsCommMonObj C.X]`, `i : C ⟶ M`,
  `[IsClosedImmersion i.hom.hom.left]`, `[Flat C.X.hom]` give the closed flat
  commutative subgroup with its actual induced group homomorphism.
- The three instances on
  `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).obj C.X).hom`
  impose smoothness and finite type on exactly `C_E`. Finite type is locally
  finite type plus quasi-compactness. The underlying pullback is the same as
  the underlying scheme of group-object base change; no unrelated generic model
  or arbitrary identification has been chosen.
- The existential `N : Grp (Over (Spec (.of D)))`, `IsCommMonObj N.X`, and
  `u : N ⟶ C` gives a commutative group and an actual group homomorphism over `S`.
  Its first three conjuncts say `Smooth N.X.hom`, `IsSeparated N.X.hom`, and
  `LocallyOfFiniteType N.X.hom`.
- `IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.map u)`
  is precisely that the canonical generic-fibre homomorphism `u_E` is an
  isomorphism, with both its source and target obtained by canonical base change.
- `∀ X : Over (Spec (.of D)), Smooth X.hom → Function.Bijective
  (fun f : X ⟶ N.X => f ≫ u.hom.hom)` is the required bijection on ordinary
  `S`-scheme Hom sets, induced specifically by composition with `u`.
  It does not restrict `X` to group schemes, affine schemes or finite type schemes.
  No quasi-compactness is imposed on `M`, `C`, `N`, or `X`.

Dependency declarations read and reused:

- `def-weil-affine-spectrum`, `def-pc-scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  and `Scheme`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme` is a Mathlib leaf without a Lean record:
  `ConnectedSpace` and the associated `connectedComponent`,
  `Mathlib.Topology.Connected.Basic`.
- `def-weil-geometric-fibre`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
  explicitly records `Over.pullback` as scheme base change and its map as the
  canonical morphism base change; this is the operation used here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj`, `IsMonHom`,
  in `Mathlib.CategoryTheory.Monoidal.Grp` and `.Mon`, with the existing
  `AlgebraicGeometry.GrpObj.onePoint` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`.
  These definitions work over arbitrary base schemes, although the node describes
  their specialization to fields. No dependency repair or duplicate definition
  is needed for this general interface.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `.QuasiCompact`, for both finite type hypotheses.

All three proof dependencies currently have neither a Lean record nor a Mathlib
match. They are not needed to type the statement and have no available modules
for proof imports: `lem-sfb-group-smoothness-identity-criterion`,
`lem-sfb-canonical-group-dilatation-defect-drop`, and
`lem-sfb-group-dilatation-universal-property`. The declaration docstring carries
all four proof steps, including finite defect descent and unique lifting.

Edge cases checked: a trivial group is permitted; an already smooth `C` admits
`N=C` and the identity map. Empty smooth test schemes give singleton Hom sets and
are included. Disconnected smooth test schemes and infinite disjoint unions are
included. Arbitrary positive and zero characteristics are allowed. No assumption
that the generic fibre is connected is inserted. A field as `D` is excluded by
exactly the node's explicit dimension-one convention, not by an unintended
restriction. Generic fibres may have dimension zero. The proof plan includes
zero initial defect and an empty bad-fibre set. Universe `u` is explicit and
`autoImplicit` is disabled.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `A flat closed subgroup of a smooth group scheme over a Dedekind domain admits a universal smoothening for morphisms from smooth schemes`:
  eight hits about ordinary scheme/algebra smoothness; no group smoothening.
- `msearch.py ... loogle '"smoothening"'`: zero hits.
- `msearch.py ... grep 'smoothen|dilatation|Neron' AlgebraicGeometry`: zero hits.
- `rg -n 'smoothen|dilatation' lean/WeilConjectures lean/Sheaf`: no hits.
- `grep -rn 'lem-sfb-lft-closed-subgroup-group-smoothening' lean/WeilConjectures`:
  no hits.
- `rg` for `group_smoothening|lft_closed_subgroup_group_smoothening` in both
  Lean roots and `dag/lean_names_upstream.json`: no hits.
- Searches for identity components located the existing field-group
  `GrpObj.onePoint` and `GrpObj.identityComponent`, with the former reused.
  The relative hypothesis is written directly with canonical fibre base change
  and `connectedComponent`, so it introduces no new notion or definition node.

Validation: `scompile.py Q140 lem-sfb-lft-closed-subgroup-group-smoothening` on the
module passed both sandbox and library-name compiles in about four seconds each,
without errors or warnings. The first compile exposed the two layers in a bundled
`Grp` homomorphism (`.hom.hom`); all four affected projections were corrected
before the successful compile. No statement correction or disputed claim.

## Second reading by Q140

A second consistency pass by the same dispatched worker (no other agents started,
as instructed; independent maintainer review is downstream) read the node and
final module together. Checked all binders and the five conclusion clauses:
Dedekind dimension is exactly one, ambient and closed subgroup structures agree,
`hM0` is equality with the whole geometric identity component, finite type occurs
only where the node requires it, `u` is a group homomorphism, and its map on Hom
sets uses ordinary `Over` morphisms and canonical composition. The generic-fibre
isomorphism uses the base change of that same `u`, not an existential unrelated
isomorphism. The bundled-hom projection errors found by compilation were fixed.
No mathematical mismatch was found; no new nodes or dependency modules were made.
