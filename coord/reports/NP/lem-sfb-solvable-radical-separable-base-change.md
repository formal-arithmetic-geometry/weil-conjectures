## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SolvableRadicalSeparableBaseChange`
states `AlgebraicGeometry.solvable_radical_separable_baseChange`, with one postponed
proof and no definitions. The node's mathematical statement is unchanged.
`stmt_deps` gains the already landed `def-sfb-semisimple-group-scheme`: its component
`IsSolvableGroupScheme` gives exactly the derived-series convention explicitly
specified in the item. No new node or dependency repair is needed.

Hypotheses and conclusions, in node order:

- The fields and extension are `(k K : Type u) [Field k] [Field K] [Algebra k K]`.
  `[Algebra.IsSeparable k K]` means that every minimal polynomial is separable;
  Mathlib's definition includes algebraicity, since the minimal polynomial of a
  nonalgebraic element is zero and is not separable. There is no finite-extension
  or Galois assumption.
- The k-group schemes are `(G R : Over (Spec (.of k))) [GrpObj G] [GrpObj R]`.
  These are group objects in schemes over k, with all group laws included.
- The ambient group is affine, finite type, smooth and geometrically connected:
  `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`,
  `[Smooth G.hom]`, and `[GeometricallyConnected G.hom]` respectively. Over a
  field the last condition is equivalently connectedness after an algebraic
  closure, as in the node. No reductivity or perfectness condition occurs.
- The specified inclusion is `(i : R ⟶ G) [IsClosedSubgroupScheme i]
  [IsNormalSubgroupScheme i]`. These existing classes include homomorphism,
  injectivity on algebra points, closed immersion, and normality of the image on
  every algebra's points, retaining the full scheme structure.
- Smoothness and connectedness of R are `[Smooth R.hom] [ConnectedSpace R.left]`;
  `(hR : IsSolvableGroupScheme R)` is finite derived length. The imported
  `groupSchemeCommutator` is xyx^-1y^-1, `IsDerivedGroupScheme` imposes the
  smallest-closed-subgroup factorization property, and `GroupSchemeDerivedLength`
  terminates at the terminal k-scheme. No arbitrary chosen subgroup is used.
- `hmax` quantifies over every k-group scheme N with a closed normal inclusion j
  into G, assuming `Smooth N.hom`, `ConnectedSpace N.left`, and
  `IsSolvableGroupScheme N`. Its conclusion `∃ f : N ⟶ R, f ≫ i = j` means
  containment as subgroup schemes. Affineness and finite type of N and R follow
  from their closed immersions into G; no redundant assumptions restrict the
  quantified subgroups.
- `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))` is the actual
  base-change functor. Its object on G or R is the stated fibre product, with
  structure map the second projection; its map on i is the canonical base-changed
  inclusion. The canonical group structure is the existing cartesian pullback
  structure, not an arbitrary group law.
- The conclusion's successive conjuncts are `IsClosedSubgroupScheme` of that
  map, `Smooth` of R_K's structure map, `ConnectedSpace` of R_K's space,
  `IsSolvableGroupScheme` of R_K, and `IsNormalSubgroupScheme` of its inclusion.
  Closedness is already part of the node's phrase “R_K ... in G_K” as a closed
  subgroup and of its last proof step.
- The final universal quantifier runs over all K-group schemes N with a closed
  normal inclusion into G_K, and the same smooth, connected and solvable
  hypotheses. Its conclusion `∃ f : N ⟶ R_K, f ≫ i_K = j` is precisely the
  asserted largest-subgroup property, as schemes rather than rational points.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, specialized
  exactly as documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  (`def-sc-group-scheme`).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` and
  `AlgebraicGeometry.IsNormalSubgroupScheme` (`def-sc-group-scheme-subgroup`).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (`def-sbc-smooth-morphisms`).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (`def-weil-connected-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  (`def-weil-finite-type-morphism`).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`
  (`def-weil-algebraic-closure`), used to check the meaning of geometric
  connectedness. `Mathlib.AlgebraicGeometry.Geometrically.Connected` supplies
  `AlgebraicGeometry.GeometricallyConnected` for that existing notion.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (`def-pc-field-extension`).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`
  (`def-pc-fibre-product`). The statement uses these through `Over.pullback`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` supplies the group structure.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `AlgebraicGeometry.IsSolvableGroupScheme`, `GroupSchemeDerivedLength`,
  `IsDerivedGroupScheme`, `groupSchemeCommutator`
  (`def-sfb-semisimple-group-scheme`, added as an existing statement dependency).
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable` for the stated extension.

Proof dependencies with recorded declarations are imported privately:
`Sheaf.AlgebraicGeometry.GaloisDescentAffineSubgroups` (descent, inclusion,
equality and normality detection),
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`
(`affine_normal_quotient_geometry`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and `.Algebra` (faithfully flat
base change and surjectivity on spectra),
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` (smooth descent), and
`Mathlib.FieldTheory.IsSepClosed` (separable closure and embeddings).
The proof-only nodes `lem-sfb-solvable-normal-subgroup-products` and
`lem-sfb-derived-commutator-word-arbitrary-field` have no recorded declaration
in the read snapshot, so there is no module to import for them. Their precise
roles are retained in the seven-step proof docstring; they are not prerequisites
for elaborating this theorem's statement.

Source check: read Milne, Algebraic Groups (2017), Proposition 19.1 and the
preceding definition of the radical, printed p.397, from the local PDF.
The proposition states separable algebraic extensions without a finiteness
restriction; its printed proof starts with the finite case. The DAG supplies the
explicit infinite-Galois descent and separable-closure argument, all seven steps
of which are included in the theorem docstring. No statement correction or
STATEMENT-DISPUTED flag is needed.

Edge cases checked before writing:

- Identity extension K=k is allowed; the conclusion recovers the same largest
  subgroup property under the canonical pullback identification.
- The trivial group and trivial radical are allowed. Derived length zero is
  terminality, not an impossible vanishing assertion about a bare type.
- For commutative smooth connected G, R=G is allowed, and maximality and base
  change have their expected meaning.
- Infinite separable algebraic and nonnormal separable extensions are allowed;
  there is no `FiniteDimensional`, `Module.Finite`, or `IsGalois` binder.
- Imperfect fields and every characteristic remain allowed. Inseparable
  extensions are excluded exactly by the node's separability hypothesis.
- Empty schemes are correctly excluded by group identity sections and by
  `ConnectedSpace`; no extra nonemptiness assumption is added.
- All fields, schemes and test algebras can be placed in any common universe u.
  This imposes no comparison between independent universes or restriction on
  which field extensions are covered. Subgroup conditions are scheme-theoretic.

Searches for existing statements and notions:

- `msearch.py ... leanfinder`: “Separable algebraic base change preserves the
  maximal smooth connected solvable normal closed subgroup of an affine group
  scheme” returned eight hits (elliptic curve point maps, smooth base change,
  formally unramified base change, cotangent comparison, absolute Galois group
  commutators, Krull topology, abelian Galois extensions, and solvable towers).
  None states the algebraic-group radical assertion.
- `msearch.py ... leansearch`: “The solvable radical of a connected algebraic
  group commutes with separable algebraic extension of the base field” returned
  eight hits: Lie-algebra radicals, relative separable closure, solvability by
  radicals, and separability over perfect fields. None is the subgroup-scheme
  assertion here.
- `msearch.py ... loogle '"GroupScheme", "solvable"'`: zero hits.
- `msearch.py ... grep 'solvableRadical|radical.*separable|separable.*radical'`:
  seven hits, in LinearAlgebra/Semisimple, FieldTheory/IsPerfectClosure, and
  AlgebraicGeometry/Morphisms/UniversallyInjective; none is this assertion.
- `rg` in `lean/WeilConjectures` for the node id found no occurrence. Searches
  in both `lean/WeilConjectures` and `lean/Sheaf` for radical/base-change names
  found no existing theorem. Searches for solvability and derived subgroups
  found `Semisimple.lean`; its full definitions were read and reused.
- `rg` in definition-node files found `def-sfb-semisimple-group-scheme` carrying
  the exact derived-series notion. The other solvable-group definitions use
  a subnormal-series interface, so no replacement or duplicate is introduced.
- `dag/lean_names_upstream.json` and both source roots have no declaration
  named `solvable_radical_separable_baseChange`.

## Second reading by NP

The dispatcher explicitly prohibits starting other agents; no independent
second worker was invoked and no independent review is claimed here. The
maintainer's independent review remains the delivery review. I reread the node
and full signature against each entry above: the smoothness, connectedness,
affineness, finite-type and separability hypotheses all occur at the stated
objects; the two maximality quantifiers cover every closed normal smooth
connected solvable subgroup, and inclusion is equality of factored embeddings.
The canonical pullback occurs consistently in every K-conclusion. The existing
solvability interface was checked through its recursion down to terminality and
the explicit commutator. No mismatch requiring a mathematical change was found.
The only metadata addition is the already landed definition dependency.

Elaboration repair: the first compile found that the canonical group-object
instance on a pullback was not active. Reading
`CategoryTheory.Functor.grpObjObj` in Mathlib showed that it is scoped to
`CategoryTheory.Obj`. Opening that existing scope, as in the recorded Galois
descent dependency, repairs elaboration without changing any hypothesis,
conclusion, construction, or signature. No local instance or helper was added.

Validation: `scompile.py NP lem-sfb-solvable-radical-separable-base-change`
compiled the delivered file successfully in sandbox mode (40.3 seconds) and as
`Sheaf.AlgebraicGeometry.GroupScheme.SolvableRadicalSeparableBaseChange`
(6.3 seconds). There were no errors or unexpected warnings. The only postponed
proof is `AlgebraicGeometry.solvable_radical_separable_baseChange`.
