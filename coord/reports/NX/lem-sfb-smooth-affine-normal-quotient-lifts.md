## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothAffineNormalQuotient` states
`AlgebraicGeometry.exists_smoothAffineNormalQuotient`, with one postponed theorem
and no new definitions. The theorem states the unchanged DAG statement. Its docstring
contains all eleven proof steps with their DAG dependencies. No node fault or
STATEMENT-DISPUTED issue was found. Only the item's `lean` field changes.

The objects are group objects in `Over (Spec (.of k))`, using the recorded group-scheme
interface, with no commutativity assumption. The field, schemes and test schemes use
universe `u`, as in the published homogeneous-quotient and subgroup interfaces.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| k-group schemes G and N | `(G N : Over (Spec (.of k))) [GrpObj G] [GrpObj N]` |
| G smooth | `[Smooth G.hom]` |
| G connected, including nonempty | `[ConnectedSpace G.left]` |
| G separated | `[IsSeparated G.hom]` |
| G finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| N smooth and connected | `[Smooth N.hom] [ConnectedSpace N.left]` |
| N affine | `[IsAffine N.left]` |
| Given closed normal subgroup inclusion | `(i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]` |
| Existence of a k-group Q and homomorphism q | Existentials `Q`, `GrpObj Q`, `q : G ⟶ Q`, `IsMonHom q` |
| Q smooth, connected, separated | `Smooth Q.hom ∧ ConnectedSpace Q.left ∧ IsSeparated Q.hom` |
| Q finite type | `LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom` |
| q smooth and surjective | `Smooth q.left ∧ Surjective q.left` |
| q finite presentation | `LocallyOfFinitePresentation q.left ∧ QuasiCompact q.left ∧ QuasiSeparated q.left` |
| The given N is the scheme-theoretic kernel | `∃ e : N ≅ GrpObj.ker q, e.hom ≫ GrpObj.kerι q = i` |
| Every k-scheme T mapping to Q | `∀ (T : Over (Spec (.of k))) (t : T ⟶ Q)` |
| Its base-change projection | `(pullback.snd q t).left` |
| Projection flat and surjective | `Flat (pullback.snd q t).left ∧ Surjective (pullback.snd q t).left` |
| Projection finite presentation | The conjunction of `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` on this same projection |
| One-member big fppf covering | `Presieve.ofArrows` of the constant `PUnit`-indexed family with this source and this projection belongs to `Scheme.fppfPrecoverage T.left` |
| Every smooth connected affine closed normal S in Q | Universal binders `S`, `GrpObj S`, `Smooth S.hom`, `ConnectedSpace S.left`, `IsAffine S.left`, `j : S ⟶ Q`, `IsClosedSubgroupScheme j`, `IsNormalSubgroupScheme j` |
| P is the actual inverse image | Existentials `P`, `GrpObj P`, `a : P ⟶ G`, `r : P ⟶ S`, with `IsPullback a r q j` |
| P is a closed normal subgroup of G | `IsClosedSubgroupScheme a ∧ IsNormalSubgroupScheme a` |
| P smooth, connected, affine | `Smooth P.hom ∧ ConnectedSpace P.left ∧ IsAffine P.left` |
| Restricted homomorphism P to S | `r` and `IsMonHom r`, with the pullback square specifying the restriction |
| Restricted homomorphism surjective | `Surjective r.left` |
| P contains the original N and the restriction has that same kernel | `∃ e : N ≅ GrpObj.ker r, e.hom ≫ GrpObj.kerι r ≫ a = i` |
| G and Q need not be affine or commutative | No `IsAffine` or `IsCommMonObj` hypothesis or conclusion for G or Q |

A cartesian square in the category of k-schemes is a fibre product of the underlying
schemes: the forgetful functor from `Over` preserves these limits. Thus the existential
`P` with `IsPullback a r q j` specifies `G ×_Q S` up to the unique isomorphism
compatible with its projections, exactly as the recorded fibre-product definition.
The final kernel isomorphism provides the inclusion
`N → ker r → P`; composing it with `a` recovers the original `i`. Its first two
factors give a closed subgroup inclusion, and its compatibility as a group
homomorphism follows from its equality after the monomorphic kernel inclusion and
the given subgroup inclusion. No merely pointwise kernel is substituted.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the relevant clause of the algebraic-closure dependency).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, and the
  `CategoryTheory.IsMonHom` group-homomorphism interface exported by its imports.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`. Its documented group-scheme/kernel convention uses
  `CategoryTheory.GrpObj.ker` and `kerι`, read in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, whose `Nonempty` field
  matches the node's convention.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` exports the recorded
  `IsSeparated` from `Morphisms.Separated`, defined by a closed diagonal.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`; its imported `AffineScheme`
  interface supplies `IsAffine`, characterized by the canonical spectrum isomorphism.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, whose
  definition is jointly-surjective flat locally finitely presented families.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`, and the fibre-product interface `IsPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Morphisms.QuasiSeparated`: `QuasiSeparated`.
  The scheme-conventions node has no independent declaration and explicitly says
  to use these existing properties as a conjunction.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, agreeing with stalkwise
  flatness by `Flat.iff_flat_stalkMap`.

Stated proof dependencies are imported with plain imports, particularly
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient.exists_homogeneousQuotient`
(the declaration itself is in namespace `AlgebraicGeometry`),
`AlgebraicGeometry.connectedSpace_of_connected_kernel` from
`Sheaf.AlgebraicGeometry.GroupScheme.ConnectedExtension`,
`AlgebraicGeometry.isAffineHom_of_fpqc_cover` from
`Sheaf.AlgebraicGeometry.FpqcAffineDescent`, and
`AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. The remaining proof
imports supply the DAG's Mathlib matches for Yoneda, descent, affine/closed
immersions, finite morphisms and base-change surjectivity.

Edge cases checked before writing:

- `N = 1`: Q can be G; the statement allows a nonaffine G and Q, for example an
  abelian variety. All kernel identifications retain the inclusion.
- `N = G`, when G is affine: Q can be the trivial group; the covering clause
  still applies to every T and the inverse-image clause gives P = G.
- `S = 1`: P is N, with its original inclusion into G. `S = Q` when Q is affine
  gives P = G, as expected from affineness of extensions.
- The empty base-change T is included, with an empty pullback and a surjective
  map to the empty space. T is not assumed reduced, affine, quasi-compact,
  connected or of finite type.
- The original group schemes cannot be empty because they have identity
  sections over a field; `ConnectedSpace` also explicitly requires nonemptiness.
- Positive characteristic is unrestricted. No argument replaces a scheme
  kernel by rational points or reduced subschemes. No commutativity is used.

Sources read: the local Milne PDF, printed pp.102--105 (quotients, kernel pairs,
faithful flatness and smoothness), pp.113--114 (subgroup correspondence and
connected extensions), and p.149 (Proposition 8.1 and its use in Proposition 8.2).
These agree with the reviewed node; no correction is necessary.

Searches for an existing statement (all made with the prescribed wrapper):

- LeanFinder: `Smooth connected algebraic group quotient by affine normal subgroup
  and affine inverse images of normal subgroups` returned eight unrelated
  Galois-category/topological quotient hits, no group-scheme theorem.
- Loogle: `GrpObj, IsNormalSubgroupScheme` returned zero hits (unknown identifier
  `GrpObj` in that service).
- Mathlib grep: `quotient|normal|extension`, subdirectory `AlgebraicGeometry/Group`,
  returned zero hits.
- LeanSearch: `Smooth surjective quotient of algebraic group by smooth affine
  normal subgroup with affine inverse image of an affine normal subgroup`
  returned eight abstract group-quotient/formal-smoothness hits, no match.
- Local `rg` for `quotient|[Nn]ormal` under
  `lean/WeilConjectures/AlgebraicGeometry/GroupScheme` found the existing subgroup
  and kernel interfaces and unrelated specific constructions, no combined theorem.
- Local `rg` for `exists.*[Qq]uotient|smooth.*[Qq]uotient` under
  `lean/Sheaf/AlgebraicGeometry/GroupScheme` found homogeneous quotient results
  without the normal-quotient and inverse-image conclusions, plus special
  reductive/Borel results. These are not duplicates.
- The required item-ID search under `lean/WeilConjectures` returned no matches.
  The proposed full declaration name was also searched in both library roots
  and `dag/lean_names_upstream.json`, with no matches.

Validation: `scompile.py NX lem-sfb-smooth-affine-normal-quotient-lifts` checked
this file in sandbox mode (4.3 seconds) and library mode (10.5 seconds), both clean.
All variables and the universe are explicit; `autoImplicit` is disabled.

## Second reading by NX

A second direct reading compared the unchanged node with the finished signature,
using the clause table above. In particular, finite presentation includes
quasi-separatedness in both occurrences; the universal test-scheme clause has no
finiteness restrictions; the pullback square specifies the inverse image; and
both kernel isomorphisms remember the original inclusion. No mismatch was found
and no correction was made. This is a self-check, not an independent agent review:
the dispatcher expressly forbids starting agents and assigns the independent
review to the maintainer.
