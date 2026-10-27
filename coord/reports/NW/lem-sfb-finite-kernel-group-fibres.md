## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FiniteKernelFibres` states
`AlgebraicGeometry.isFinite_fiber_and_krullDim_le_zero_of_isFinite_kernel` with
one whole-theorem `sorry`. No definition, auxiliary theorem, statement correction,
or dependency repair is needed. The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- The arbitrary field k is `{k : Type u} [Field k]`, with `u` explicitly declared.
- The k-group schemes G and H are `{G H : Over (Spec (.of k))}` with
  `[GrpObj G] [GrpObj H]`. These are general group objects, with no commutativity,
  smoothness, reducedness, connectedness, or properness assumption.
- Finite type of each group scheme is `[LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]` and the corresponding two instances for H. This is
  precisely the conjunction recorded on def-weil-finite-type-morphism.
- The group-scheme homomorphism is `(f : G ⟶ H) [IsMonHom f]`: the morphism in
  the over category is over k and the instance expresses compatibility with
  multiplication (and identity; for groups inverse compatibility follows).
- The scheme-theoretic kernel finite over k is `[IsFinite (GrpObj.ker f).hom]`.
  The recorded upstream `GrpObj.ker` is the pullback of f along the identity
  section in the over category, whose underlying square is the required
  scheme-theoretic square, retaining nilpotents.
- The arbitrary point is `(y : H.left)`. No rationality or closedness is required.
- Finiteness of G_y over κ(y) is `IsFinite (f.left.fiberToSpecResidueField y)`.
  `f.left.fiber y` is the pullback along `H.left.fromSpecResidueField y`, and
  this structure morphism is its second projection to
  `Spec (H.left.residueField y)`. Thus the assertion concerns the entire scheme
  fibre, not just finiteness of its underlying set.
- The dimension clause is `topologicalKrullDim (f.left.fiber y) ≤ 0`.
  Its codomain is `WithBot ℕ∞`, so bottom gives the specified dimension of the
  empty scheme. The two conclusions form a conjunction for every point y.
- There are no surjectivity, equal-dimension, properness, smoothness or
  connectedness hypotheses. The signature contains no implicit extra test
  objects or chosen rational points.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs (Mathlib match).
- def-sc-group-scheme: `CategoryTheory.GrpObj` from
  Mathlib.CategoryTheory.Monoidal.Grp; `CategoryTheory.IsMonHom` from
  Mathlib.CategoryTheory.Monoidal.Mon; `CategoryTheory.GrpObj.ker` from
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. The existing
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents these exact
  specializations and supplies their interfaces through the public import.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` from
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and `AlgebraicGeometry.QuasiCompact`
  from Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, applied to structure maps.
- def-weil-residue-field: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`
  from Mathlib.AlgebraicGeometry.ResidueField. The fibre projection already
  specifies the appropriate residue field without introducing a second notion.
- def-pc-scheme-fibre: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, Mathlib.AlgebraicGeometry.Fiber.
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite, for the kernel structure morphism
  and the fibre structure morphism.
- def-kun-topological-krull-dimension: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension, literally the supremum of chain lengths of
  nonempty irreducible closed subsets.

Proof-only imports retain the prescribed proof plan:
`AlgebraicGeometry.isFinite_of_fpqc_cover` in
WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover;
`AlgebraicGeometry.IsFinite.locallyQuasiFinite_and_quasiCompact` in
WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite; and
`Scheme.Hom.IsQuasiFinite` (and the other recorded predicates) in
WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism. The former publicly
imports Mathlib.AlgebraicGeometry.Sites.Fpqc (`Scheme.fpqcPrecoverage` and
flatness); the group-scheme import publicly supplies the finite morphism
base-change instance of Mathlib.AlgebraicGeometry.Morphisms.Finite and the
pullback interface. No proof-dependency import cycle is introduced.
The docstring carries all five proof steps, including the field extension
needed to obtain a point, inverse translation morphisms, base-change
finiteness, fpqc descent, and the dimension argument.

Source checked: Milne, Abelian Varieties, Chapter I Proposition 7.1, printed
p.32, first proof paragraph, especially the translation of a fibre after
extension of scalars. The existing stage-1 node expands this argument to
arbitrary group schemes using only the group law, with Stacks 01WL and 02LA
for finite base change and descent. The statement does not assert that the
original fibre has a κ(y)-rational point.

Edge cases checked mathematically before writing:

- A point outside the image has an empty fibre; the zero algebra is finite,
  and `topologicalKrullDim` uses bottom for the empty space.
- The identity homomorphism has trivial finite kernel and one-point fibres.
- A non-surjective closed subgroup inclusion is allowed; this checks that
  the conclusion does not silently require an isogeny.
- Frobenius on the additive group in characteristic p has finite nonreduced
  kernel α_p. The statement retains the scheme structure of its fibres.
- A generic or non-rational target point is allowed. A nonempty fibre may
  require an extension L of κ(y) for translation; the proof explicitly uses
  the residue field of a point of the fibre.
- A zero-dimensional or disconnected group is not excluded. All finite-type
  assumptions are retained even though the fibre translation argument needs
  less. No fixed characteristic or algebraic closedness is assumed.

Searches for an exact existing theorem (2026-10-24):

- msearch.py leanfinder: "A homomorphism of finite type group schemes over a
  field with finite scheme theoretic kernel has finite scheme theoretic
  fibres". Eight hits, including finite-morphism fibre cardinality and
  discreteness, `IsFinite.finite_preimage_singleton`, and abstract
  `Group.fintypeOfKerOfCodom`. None deduces finite scheme fibres from a finite
  group-scheme kernel.
- msearch.py loogle: `AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Scheme.Hom.fiber`. Two hits: the finite fibre projection
  instance under locally quasi-finite and quasi-compact hypotheses, and
  `locallyQuasiFinite_iff_isFinite_fiber`. Neither has the group-scheme
  finite-kernel hypothesis.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `ker.*[Ff]inite|[Ff]inite.*ker|[Ff]iber.*[Tt]ranslat`: zero hits.
- msearch.py leansearch: "A homomorphism of group schemes over a field with
  finite kernel has finite scheme theoretic fibres". Eight hits, concerning
  finite morphisms, abstract finite groups, and ideal-sheaf kernels. No match.
- rg of WeilConjectures and Sheaf for the kernel/finite/translation patterns,
  followed by focused searches in AlgebraicGeometry/GroupScheme: group
  scheme definitions and stronger isogeny or reductive-group contexts, but
  no exact theorem. Search for the item id in WeilConjectures: no hit.
- rg of Mathlib, WeilConjectures and Sheaf for
  `finite_kernel.*fiber|finite_fiber.*ker|isFinite_fiber.*ker`: no hit.
  The proposed full declaration name is new.

Validation: `scompile.py NW lem-sfb-finite-kernel-group-fibres` compiled the
module on the server both as a sandbox and at its library module path, with
exit code zero and no reported warnings or errors. All universes and variables
are explicitly bound. No STATEMENT-DISPUTED issue was found.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
