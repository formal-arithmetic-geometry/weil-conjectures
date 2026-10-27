## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricRegularityAffineCover` states
`AlgebraicGeometry.geometricRegularity_affineCover_tfae`, with `sorry` as its
entire proof. No new definitions, dependency repairs, or statement corrections
are needed. The source read was Stacks `varieties.tex`,
`lemma-geometrically-regular`, Tag 038V, including its proof. The node's test
by all finite extensions lies between the source's finitely generated test and
finite purely inseparable test, so the stated equivalence is exactly the node.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The locally Noetherian scheme is `(Z : Scheme.{u}) [IsLocallyNoetherian Z]`.
- Its given k-scheme structure is `(f : Z ⟶ Spec (CommRingCat.of k))`.
  An explicit map is used because the statement involves its base changes.
- Condition (1) is the first entry of `List.TFAE`: for every `K : Type u`
  with `[Field K] [Algebra k K] [Module.Finite k K]`, the scheme
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))` satisfies
  `IsRegularScheme`. This quantifies over all finite extensions, including
  the identity extension, and does not require purely inseparable extensions.
- Condition (2) is `∀ W : Z.affineOpens, ...`. The ring is exactly
  `Γ(Z, W.1)`. Its k-algebra structure is supplied explicitly to the recorded
  `Algebra.IsGeometricallyRegular`: apply `RingHom.toAlgebra` to the composite
  `(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
  Z.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op`.
  These maps are respectively k to sections of Spec k, the structure map on
  global sections, and restriction to W. No arbitrary algebra action is assumed.
- Condition (3) is `∃ S : Set Z.affineOpens, (⨆ W ∈ S, W.1) = ⊤ ∧ ...`.
  Its final universal quantifier requires the same geometric regularity
  predicate with the same induced algebra structure for every member W of S.
  A set of affine opens is an affine open cover; any indexed cover has the same
  image set, and conversely S is indexed by its subtype. There is no finiteness
  or nonemptiness assumption, and discarding repeated opens changes no clause.
- `List.TFAE` asserts pairwise equivalence of all three propositions, exactly
  the three equivalent conditions in the node.

Dependencies were read in the DAG and in their recorded source declarations:

- `Field`, `Mathlib.Algebra.Field.Defs`, for `def-weil-field` (a Mathlib leaf).
- `AlgebraicGeometry.Scheme` and `Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme`,
  for `def-pc-scheme`.
- `AlgebraicGeometry.IsLocallyNoetherian`, `Mathlib.AlgebraicGeometry.Noetherian`,
  for `pqf-def-locnoeth`; its field quantifies over all affine opens.
- `CategoryTheory.Limits.pullback`, with `pullback.fst` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, for
  `def-pc-fibre-product`; scheme pullbacks are supplied by the public import
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `AlgebraicGeometry.IsRegularScheme`, `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  for `def-weil-regular-scheme`. This is the recorded conjunction of local
  Noetherianity and the upstream stalkwise `IsRegular`; the latter alone would
  omit part of the node's regular-scheme notion.
- `Algebra.IsGeometricallyRegular`, `WeilConjectures.RingTheory.GRing`, for
  `def-weil-pbc-g-ring`. Its definition includes Noetherianity and tests regular
  tensor products against finite purely inseparable extensions.

The recorded, available proof interfaces are imported without `public`:
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`
(`Scheme.finite_affine_tensor_base_change`),
`WeilConjectures.RingTheory.GeometricallyRegularFieldExtension`
(`Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular`),
`Mathlib.AlgebraicGeometry.Restrict` (`isPullback_morphismRestrict`), and
`Mathlib.RingTheory.TensorProduct.Maps` (the algebra tensor universal property).
The remaining affine-chart, affine-basis, affine-stalk, and affine Noetherianity
proof dependencies are supplied by `Mathlib.AlgebraicGeometry.AffineScheme` and
`Mathlib.AlgebraicGeometry.Noetherian`, already publicly imported through the
statement dependencies. The theorem's docstring carries all six proof steps,
including these dependency ids and the zero-ring case.

Edge cases checked before writing:

- Z may be empty; there is no `Nonempty` assumption on its carrier or covering.
  S may be empty, with the supremum condition becoming bottom = top, precisely
  the empty-space case.
- The empty affine open has zero section ring. `CommRing`, the induced algebra,
  and `Algebra.IsGeometricallyRegular` allow this ring; no `Nontrivial` is added.
- The identity field extension is included. There is no characteristic,
  perfectness, reducedness, finite type, or separatedness assumption.
- The index set is an unrestricted set of all affine opens, so covers are
  neither restricted to finite nor countable ones. Any indexed cover can be
  replaced by its image set without altering its union or its local condition.
- The common universe u follows the scheme category's Spec and pullback API.
  Finite extensions admit a representative in the base field's universe
  (finite vector spaces are small); testing these representatives loses no
  extension. The geometric-regularity dependency itself tests extensions in
  `Type (max u u)`, exactly `Type u` here. No independent lower universe creates
  a vacuous extension test.

Searches for an existing statement (all via the prescribed msearch wrapper):

- `leanfinder`: "Geometric regularity of a locally Noetherian scheme over a field
  is equivalent to geometric regularity of all affine coordinate algebras and of
  an affine open cover". Eight results were Noetherian affine-cover and related
  locality lemmas; none states this geometric-regularity criterion.
- `loogle`: `"GeometricallyRegular"`. Zero results.
- `grep`, Mathlib AlgebraicGeometry: `geometrically.?regular|geometric.?regular`.
  Zero results.
- `leansearch`: "A locally Noetherian scheme over a field is geometrically regular
  if and only if every affine coordinate ring is geometrically regular". Eight
  results concern local Noetherianity or Artinianity, with no equivalent result.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `geometrically.?regular|geometric.?regular|IsGeometricallyRegular`, followed by
  file-name searches restricted to AlgebraicGeometry: existing ring statements
  and the recorded ring predicate were found; no scheme affine-cover criterion.
- The required item-id search on `lean/WeilConjectures` returned no match.
  The chosen declaration name is new. The upstream compact-object example and
  its DAG record were read; its former Sheaf module is withdrawn, so the actual
  upstream `WeilConjectures.CategoryTheory.CompactObject` was also read.

Validation: compiled with the required `scompile.py`, both its sandbox-name and
library-name checks, against the published live library. Final delivery preflight
and per-file compilation are run by `deliver2.py --no-push` before delivery.
No node faults or statement disputes were found.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
