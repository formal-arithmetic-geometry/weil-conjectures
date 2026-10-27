## Worker report

The module `Sheaf.AlgebraicGeometry.MultiplicativeTypeEtaleSplitting` states
`AlgebraicGeometry.multiplicativeType_etale_splitting`, with `sorry` as its sole proof.
The statement is unchanged. The definition module constructs the missing arbitrary-base
`D_S(M)` from the existing integral Hopf-spectrum model, with actual data.

Source read: Conrad, Reductive group schemes, Proposition B.3.4, printed pp.291–292,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf (PDF pages 290–291, zero based).
The proposition allows an arbitrary base scheme and fppf forms of diagonalizable groups
of finite type. Its first assertion is exactly the splitting used here; refinement by
affine opens gives the affine members required by the node. The stronger classification
and henselian-base assertions in Conrad are not part of this node. The node's alternative
isomorphism-sheaf proof is preserved, in eight steps, in the theorem docstring.

Clause correspondence:

- The base scheme is `U : Scheme.{u}`.
- The group object with multiplication, identity, inverse and their diagrams is
  `H : Grp (Over U)`; no commutativity, smoothness or affineness is assumed of H.
- The given fppf covering is `V : U.Cover.{u} Scheme.fppfPrecoverage`.
  Mathlib's covering record includes joint surjectivity and membership in the
  precoverage of flat locally finitely presented morphisms, without quasi-compactness.
- The additive abelian groups are bundled as `M : V.I₀ → AddCommGrpCat.{u}`.
  `hM : ∀ i, AddGroup.FG (M i)` is exactly finite generation, independently per member.
- `hsplit` is the family of `Nonempty` isomorphism types from the base-changed group
  `(Over.pullback (V.f i)).mapGrp.obj H` to
  `relativeDiagonalizableGroup (V.X i) (M i)`. Isomorphisms are in `Grp (Over (V.X i))`:
  they preserve all group operations, rather than only the underlying schemes.
- The existential `W : U.Cover.{u} Scheme.etalePrecoverage` gives jointly surjective
  etale maps `W.f j : W.X j ⟶ U`.
- `∀ j, IsAffine (W.X j)` is the affine-member condition.
- `N : W.I₀ → AddCommGrpCat.{u}` and `AddGroup.FG (N j)` give the required character
  groups; the concluding `Nonempty` group-object isomorphism gives every splitting.
- No Noetherian, reduced, smooth, connected, henselian, finite-cover, positive-rank,
  invertible-torsion or characteristic assumption occurs. The universe u is explicit;
  cover indices and character groups are sets in the same size convention as schemes.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` (and the recorded
  generated `Scheme.fppfTopology`). We use the covering-family declaration, since
  the node assumes a covering family, rather than merely a covering sieve.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documentation and
  `baseChange_morphism_projections` identify base change with `Over.pullback`, which
  is used here with its `mapGrp` functor, preserving the group structure.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`: `ringDiagonalizableGroup`, read
  together with `ringDiagonalizableGroupMap`; the latter is not required in this signature.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used by
  `Scheme.etalePrecoverage` from `Mathlib.AlgebraicGeometry.Sites.Etale`.
- New dependency `def-sfb-relative-diagonalizable-group`:
  `Sheaf.AlgebraicGeometry.RelativeDiagonalizableGroup`, `relativeDiagonalizableGroup`.

The already stated proof dependencies are imported privately. Mathlib supplies the
pullback-spectrum formula, tensor pushout, affine adjunction, morphism gluing,
affine open covers, scheme coproducts and etale composition; the published project
supplies the source/target properties, algebraic spaces and fpqc etale descent.
Unstated proof-only nodes (relative character duality and fppf atlas bootstrap) need
no additional statement dependency or theorem in this stage-2 delivery.

Edge cases checked before writing: empty U admits an empty index set in both cover
records; no Nonempty instance is required. The zero character group gives the trivial
group; arbitrary finite torsion, including p-torsion in characteristic p, is admitted.
Character groups and ranks may vary among members. Nonreduced/disconnected/non-Noetherian
bases and zero rings on empty affine opens are allowed. The integral model is the
existing Hopf spectrum over `ULift.{u} ℤ`, base changed along the unique map from S;
there is no arbitrary choice of a group scheme. Its affine coordinate identification
is `A ⊗[ℤ] ℤ[M] ≃ A[M]`, sending `a ⊗ e_m` to `a e_m`, which respects multiplication,
coproduct, counit and antipode. Thus the construction agrees with the specified gluing.

Searches actually run:

- msearch LeanFinder: “An fppf locally diagonalizable group scheme is split on an
  etale cover”: eight general etale/diagonal declarations, no splitting theorem.
- msearch Loogle: `diagonalizable, Grp, Over`: zero hits, with unknown identifier
  `diagonalizable`; this query alone is inconclusive.
- msearch grep in AlgebraicGeometry: `diagonali[sz]able|multiplicativeType`: zero hits.
- msearch LeanSearch: “Diagonalizable group scheme over an arbitrary scheme base”:
  eight hits (Rep.diagonal, Representation.diagonal and general scheme diagonal/affine
  declarations), no arbitrary-base construction.
- msearch LeanFinder: “Base change of the integral group algebra defines a
  diagonalizable group scheme”: eight representation-theory hits, no group scheme.
- msearch grep in AlgebraicGeometry:
  `relativeDiagonalizableGroup|schemeDiagonalizable|diagonali[sz]able`: zero hits.
- `rg` over `lean/WeilConjectures` for diagonalizable/multiplicativeType and the
  item id: no match; `rg` over `lean/Sheaf` found the affine ring construction and
  field-only diagonalizable and multiplicative-type constructions, not this theorem
  or arbitrary-base construction. All definition-node statements containing
  “diagonaliz” were inspected; none introduces this arbitrary-base group scheme.
  `tools/blueprint_refs.py search diagonalizable` returned zero blueprint nodes.

Both delivered modules compiled cleanly through scompile.py, each separately in
module mode against the live published build. No diagnostic commands remain.
No statement dispute or source correction was needed.

## New nodes

`def-sfb-relative-diagonalizable-group` defines D_S(M) for any scheme and additive
abelian group, using the unique S → Spec Z and the integral model of
`def-sfb-ring-diagonalizable-group`. The source is Conrad Appendix B.1, printed p.280;
the base-change description has affine Hopf algebra A[M], so it is the specified
object obtained by gluing affine diagonalizable groups. The searches above found
only affine or field-base constructions; the new definition reuses the affine one
rather than duplicating it. Its three statement dependencies are schemes, base
change, and the affine diagonalizable group. It has no postponed proof or hollow data.

## Second reading by Q143

This is the author's second reading; the maintainer supplies the independent review.
I reopened the node and both modules and checked each clause against the signature.
The input and output cover records encode joint surjectivity and the correct morphism
properties; affine members occur only in the conclusion. M and N are additive abelian
groups, with finite generation stated at every index; no torsion restriction is hidden
in their bundled types. `mapGrp.obj H` base changes the actual group operations and the
isomorphism category is over the correct cover member. I checked that the new definition
pulls back along S → Spec Z (not the reverse map) and that its model is Z[M], with the
recorded Hopf operations. Cover indices can be empty, and no extra finite/nonempty or
base-regularity condition is present. No mismatch required a statement correction.
