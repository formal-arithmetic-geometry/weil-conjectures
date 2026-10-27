## Worker report

The module `Sheaf.AlgebraicGeometry.CommutativeTorsorPositiveWeight` states
`AlgebraicGeometry.commutative_torsor_positive_weight`, with its sole proof `sorry`.
There are no new definitions, extra nodes, dependency repairs, or statement corrections.
The node copy changes only `lean`.

Source read: Milne, Algebraic Groups (2017), Lemma 8.22 and its proof, printed p.152.
Although the printed lemma says “an integer”, the proof gives either 1 or the positive
finite separable degree. Its difference morphisms and their Galois sum give the scheme
morphism identity in the node. The node's proof instead sums over the entire finite
Galois group, allowing repeated conjugate points; this also gives a positive weight.
The declaration docstring carries all seven node proof steps and their dependencies.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`.
- The k-group scheme is `H : Over (Spec (.of k))` with `[GrpObj H]`.
  This is exactly the existing group-scheme encoding documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- Commutativity is `[IsCommMonObj H]`; its axiom says that swapping the two factors
  leaves multiplication unchanged.
- Smoothness is `[Smooth H.hom]`, separatedness `[IsSeparated H.hom]`, and finite
  type is `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`.
- Geometric integrality is `[GeometricallyIntegral H.hom]`. Mathlib defines this
  using `IsIntegral` after every map Spec E to the base, with E a field. Over Spec k
  these maps are precisely field extensions of k. `IsIntegral` includes nonemptiness,
  so this matches the node's explicit “nonempty and integral”, including E=k.
- The finite-type k-scheme V is the second object of
  `(H V : Over (Spec (.of k)))`, with `[LocallyOfFiniteType V.hom] [QuasiCompact V.hom]`.
- The right action is the specified k-morphism `(a : V ⊗ H ⟶ V)`. In this over category
  the tensor product is the actual chosen fibre product over Spec k.
- Unitality is `hunit`: for every test k-scheme T and point v, `lift v 1 ≫ a = v`.
  The point `1 : T ⟶ H` is the group identity section composed with the structure map.
- Associativity is `hassoc`: `(v.g).h = v.(g*h)` on every test k-scheme, written
  `lift (lift v g ≫ a) h ≫ a = lift v (g * h) ≫ a`. By Yoneda these are exactly the
  action diagrams: the source of each diagram itself is among the test objects.
- Flatness and surjectivity of V to Spec k are `[Flat V.hom] [Surjective V.hom]`.
- The torsor isomorphism is `[IsIso (lift (fst V H) a)]`. The source is V times H
  and the target is V times V, and its two components are precisely pr1 and a.
  Isomorphisms in the over category are exactly isomorphisms of the underlying
  schemes over the base. No rational point is part of the data or hypotheses.
- The positive integer is `∃ (n : ℕ), 0 < n ∧ ...`.
- The k-scheme morphism is `∃ (φ : V ⟶ H), ...`.
- The identity of morphisms V times H to H is
  `a ≫ φ = lift (fst V H ≫ φ) (snd V H ≫ (𝟙 H ^ n)) ≫ μ[H]`.
  Here `μ[H]` is the group multiplication and `𝟙 H ^ n` is its repeated-sum map,
  exactly as documented by the group-scheme dependency. Mathlib uses multiplicative
  notation for the pointwise group on morphisms; no multiplication in the field is
  involved. Evaluating this equality on T-points gives phi(v+h)=phi(v)+nh, for every
  k-scheme T; that final sentence of the node is an equivalent reading of this same
  equality, not a separate assertion restricted to rational points.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs` (commutative ring and
  division-ring structure, hence nontrivial).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`; `CategoryTheory.MonObj` and
  `CategoryTheory.IsCommMonObj` in `Mathlib.CategoryTheory.Monoidal.Mon`;
  `CategoryTheory.GrpObj.Hom.group` in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`; and pointwise multiplication
  `CategoryTheory.MonObj.Hom.mul_def` in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mon`.
  The public import `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` supplies
  these recorded interfaces and explicitly documents the over-category convention
  and multiplication-by-n convention.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, imported publicly.
- `def-weil-pbc-scheme-conventions` is a convention record, not a declaration.
  Its properties used here are `AlgebraicGeometry.IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, and `Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`. These are exposed by the
  statement imports.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties`, used through the existing
  `AlgebraicGeometry.GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, imported publicly.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The existing
  `CategoryTheory.Over.cartesianMonoidalCategory` from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` uses these actual pullbacks;
  `Over.tensorObj_left`, `Over.fst_left` and `Over.snd_left` identify the notation.

All recorded proof dependencies have their modules imported plainly, including:
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` for smooth fpqc descent;
`WeilConjectures.AlgebraicGeometry.DensePoints`;
`WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions`;
`WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition`;
`WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct`;
`WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend`; and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`. The already exposed Proper, Smooth,
Fpqc and group-scheme modules also supply the corresponding proof dependencies.
No proof import is omitted for a cycle.

Edge cases checked before writing:

- The empty V is excluded by the stated surjectivity over the nonempty field spectrum.
  Empty H is excluded by geometric integrality (and by the identity section).
- The trivial group is allowed. Its nonempty torsor is trivial and the unique
  morphism has weight one; no positive-dimension hypothesis occurs.
- A torsor having no k-point is allowed. Neither action law supplies such a point;
  the laws quantify over points that exist on each test scheme.
- In positive characteristic the weight may be divisible by the characteristic;
  no invertibility or prime-to-characteristic restriction is imposed, and [n] is
  still a morphism even if it is zero on a particular group.
- If V has a k-point the inverse translation has weight one, as in the source.
- All universes are explicit, with `set_option autoImplicit false`. Schemes and
  fields lie in the common arbitrary universe u, including all test schemes needed
  to express the action laws by Yoneda. The geometric-integrality interface tests
  fields in this same universe, so there is no vacuous smaller test universe.

Searches actually run:

- `msearch.py leanfinder`, query “A torsor under a smooth commutative algebraic group
  over a field admits a scheme morphism to the group equivariant for multiplication
  by a positive integer”: 8 hits, all AffineSpace constructions or their point
  equivalences; none is this scheme-morphism existence statement.
- `msearch.py leansearch`, query “A torsor under a commutative algebraic group over
  a field admits a regular morphism to its group equivariant for multiplication by
  a positive integer”: 8 hits, including `AddTorsor`, its constructors,
  `Equiv.vaddConst` and additive-circle torsion results; none addresses a scheme
  morphism or descent of an algebraic torsor.
- `msearch.py loogle`, query `"GrpObj", "Hom"`: 12 hits, including
  `CategoryTheory.GrpObj.inv_hom`, `mulRight_hom` and tensorHom identities; these
  describe existing group-object maps, not positive-weight maps from torsors.
- `msearch.py grep`, query `torsor|Torsor`, Mathlib subdirectory `AlgebraicGeometry`:
  zero hits.
- `rg -n 'positiveWeight|positive_weight|torsor|Torsor'` on both project roots
  `WeilConjectures` and `Sheaf`: existing finite constant-group etale torsors,
  sheaf torsors, and split-solvable torsor results, but no statement of this lemma.
  Read `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`: its
  `RepresentedRightTorsor` packages general torsors with finite-presentation data;
  this statement writes exactly its own given action and laws using the existing
  categorical group operations, without introducing any new torsor definition.
- `rg -n 'lem-sfb-commutative-torsor-positive-weight'` on `WeilConjectures`: no hit.
- `rg -l 'positive.weight|positive_weight|positiveWeight|Lemma 8.22|commutative_torsor_positive_weight'`
  on both project roots located `AbelianVariety.MultipleRetraction`; read it. That
  theorem cites this missing lemma in its proof plan but states an abelian-inclusion
  retraction, not a statement about arbitrary torsors. Other hits concern unrelated
  weights in formal algebra and Picard calculations.

Validation: scompile.py compiled the sandbox and library forms cleanly, in 1.9 s and
1.7 s respectively, against the published live server library. The file contains
exactly one theorem with `sorry`; no definitions or proved auxiliary facts.
No disputed statement or node fault was found.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
