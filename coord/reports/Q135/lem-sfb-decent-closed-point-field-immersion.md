## Worker report

Item: lem-sfb-decent-closed-point-field-immersion. The single new module
`Sheaf.AlgebraicGeometry.DecentClosedPointFieldImmersion` states
`AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_field_of_decent`.
Its only proof is `sorry`; it defines no new notion. The node changes only in `lean`.
There are no statement corrections, dependency repairs, new nodes or disputed statements.

Source checked: `literature/stacks-project/decent-spaces.tex`,
`lemma-decent-space-closed-point` (Tag 0AHB, lines 3418–3450),
`definition-very-reasonable` (03I8) and `lemma-UR-finite-above-x` (03JV), condition (6).
The source's decency hypothesis is precisely the all-field-maps quasi-compactness
hypothesis expanded in this node. The docstring records all five proof steps and their
DAG dependencies, including the empty chart fibre.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`.
- An algebraic space over S: `(X : AlgebraicSpace S)`. This is the existing full
  subcategory of fppf sheaves with representable diagonal and an etale surjective atlas;
  `X.obj.obj` is its underlying presheaf. The base scheme is unrestricted.
- Field-valued point classes and atlas topology: `(x : Point X.obj.obj)` uses the
  existing quotient by common field extensions; `AlgebraicSpacePointTopology` supplies
  the final topology under etale scheme charts. No new point set or topology is introduced.
- A field and its spectrum: the universal binders `(K : Type u) [Field K]` and
  `Spec (CommRingCat.of K)` use Mathlib's field and affine-spectrum notions. Universe u
  is the existing test-scheme/field size convention of AlgebraicSpace S.
- Every field-valued S-morphism: the `hdecent` binders `b : Spec ... ⟶ S` and
  `c : yoneda.obj (Over.mk b) ⟶ X.obj.obj` quantify over every base structure and every
  such map. Yoneda natural transformations on `Over S` are exactly the S-morphisms here.
- Every affine scheme test U to X: `(U : Over S), IsAffine U.left →
  ∀ t : yoneda.obj U ⟶ X.obj.obj` in `hdecent` includes all affine sources and all maps,
  not only etale charts or members of a chosen atlas.
- The scheme fibre product is quasi-compact: the witnesses
  `∃ (V : Over S) (p : V ⟶ U) (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
  IsPullback q (yoneda.map p) c t ∧ CompactSpace V.left` identify V with the actual
  presheaf pullback, and require its underlying scheme space to be quasi-compact.
  `CompactSpace` imposes no Hausdorff condition. Such scheme representability is already
  guaranteed by the algebraic-space diagonal (both sources are schemes); it adds no
  restriction to quasi-compactness. Isomorphism invariance makes the existential choice
  of representing pullback immaterial. This is the identical affine-test hypothesis
  used by the landed consumer `finite_of_decent_of_finite_residueField` in
  `Sheaf.AlgebraicGeometry.DecentSpaceFiniteFieldMap`.
- The point is closed: `(hx : IsClosed ({x} : Set (Point X.obj.obj)))` is exactly
  closedness of its singleton in the imported atlas topology.
- Existence of a field K: `∃ (K : Type u) (_ : Field K)` retains nontriviality,
  arbitrary characteristic and arbitrary field extension degree.
- Existence of an S-morphism i from its spectrum: the existential `b` and
  `i : yoneda.obj (Over.mk b) ⟶ X.obj.obj` retain the structure map to S explicitly.
- Its image is precisely {x}: `pointImage i = {x}` uses the dependency's point image,
  defined by all field-valued representatives in the source. Equality ensures both
  containment and occurrence of x. It is not merely a chosen map with unspecified image.
- Representable closed immersion: `IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) i` quantifies over every scheme T over S and
  every `h_T → X`. Its witnesses give an actual scheme-valued pullback square, and its
  scheme projection is a Mathlib closed immersion. Thus both representability and the
  full closed-immersion property are present; the conclusion is not restricted to affine
  or etale test schemes.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `IsAlgebraicSpace`. The first is the recorded
  algebraic-space notion; the second states the scheme-test conclusion directly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` and `AlgebraicSpace.pointImage`; its public
  dependency `AlgebraicSpacePointClasses` provides `Point`, `PointRepresentative`,
  their common-extension relation and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback` and
  `etale_fibreProduct_isScheme`. Read all three statements and docstrings; the module
  is a public statement-dependency import for the given fibre-product framework.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
  These are the recorded Mathlib matches, exposed through the public dependencies.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  also `isClosed_singleton_iff_isClosedImmersion` for the proof plan's closed residue point.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` in the statement and
  `Scheme.isBasis_affineOpens` in the proof plan.
- Plain proof imports: `Mathlib.AlgebraicGeometry.ResidueField`, providing
  `Scheme.SpecToEquivOfField`,
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, and
  `Scheme.fromSpecResidueField_apply`;
  `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`, providing
  `Scheme.Hom.etale_fibre_discrete_separable_points`;
  `WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion`, providing
  `fieldPoint_factorsThrough_immersion`. Read each full signature and docstring.
- Proof-only nodes without recorded Lean declarations are not restated or imported:
  lem-sfb-decent-quasicompact-monomorphic-points,
  lem-sfb-decent-etale-fibres-no-specializations,
  lem-sfb-monomorphism-into-field-coproduct,
  lem-sfb-space-closed-immersion-atlas-locality. They are named in the proof docstring.
  None is needed to elaborate the statement.

Edge cases checked before writing:

- Empty X admits no x, so the theorem has no impossible field-existence demand there.
- Empty test scheme U or T is allowed. Its pullback is empty, is quasi-compact,
  and its projection is a closed immersion. The finite decomposition argument includes
  zero components.
- Arbitrary nonreduced test schemes, non-Noetherian bases, non-quasi-separated spaces,
  and infinite atlases are allowed. No extra separation or finiteness assumptions occur.
- All field characteristics, imperfect fields, and inseparable extensions are allowed.
  No algebraic-closedness, finite-degree or residue-field hypothesis was introduced.
- Universal field and scheme tests use the same universe u as S and the existing big
  site, not a smaller independent universe. The point quotient has its existing u+1 size.
- The field is nonzero by `Field`; the conclusion therefore really represents the
  specified point, while the image equality also rules out an empty image.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder "A closed point of a decent algebraic space is a
  representable closed immersion from a field spectrum"`: eight hits, led by
  `isClosed_singleton_iff_isClosedImmersion`, residue-field immersions and
  `Scheme.SpecToEquivOfField`. These concern schemes and do not supply this result
  for algebraic spaces.
- `msearch.py ... loogle "AlgebraicSpace, IsClosedImmersion"`: zero hits,
  unknown identifier AlgebraicSpace (not a Mathlib notion).
- `msearch.py ... grep "AlgebraicSpace|residual[Gg]erbe|[Dd]ecent" AlgebraicGeometry`:
  zero hits in Mathlib's algebraic geometry.
- `msearch.py ... leansearch "A closed point of a decent algebraic space is the image
  of a closed immersion from the spectrum of a field"`: eight hits on closed points,
  scheme closed immersions and scheme residue-field maps; no algebraic-space match.
- `rg -n -i 'decent|closed point.{0,50}algebraic space|closed point.{0,40}field spectrum|
  closed.*field subspace' lean/Sheaf lean/WeilConjectures`: related modules concern
  finite field maps, algebraic field image closedness, reduced singleton factorization,
  and other decent-space results. Read `DecentSpaceFiniteFieldMap`,
  `DecentAlgebraicFieldImageClosed` and `ReducedSingletonFieldFactorization`:
  the first cites this item in its proof; the second assumes quasi-compact monomorphic
  representatives and proves image closedness; the third assumes a field monomorphism
  and proves reduced-source factorization. None proves existence of the closed field
  immersion here.
- Exact id/name searches in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing declaration of this statement. The id
  occurs only in the downstream finite-field-map proof docstring.
- Read the existing `MapIsQuasiCompact` in `ProperCurveModuli` and
  `IsQuasiCompactPresheafMap` in `SpaceQCSeparatedEtaleLocal`. They are general
  algebraic-space/presheaf predicates, not this theorem. The present statement spells
  out its node's actual scheme pullback and `CompactSpace` condition inline, as its
  landed consumer does, and creates no competing definition.

Validation: the prescribed scompile.py invocation compiled this file in both sandbox
and library-module modes against the server build, cleanly (5.3 s and 4.3 s).
The module explicitly disables autoImplicit, declares its universe and binds all
variables. All Lean lines are at most 93 characters. Delivery preflight follows.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
