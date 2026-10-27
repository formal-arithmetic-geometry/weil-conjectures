## Worker report

The module `Sheaf.AlgebraicGeometry.DecentSpaceFiniteFieldMap` states
`AlgebraicGeometry.AlgebraicSpace.finite_of_decent_of_finite_residueField` with
`sorry`. No definitions, additional nodes, or statement changes are needed.

The source was read directly in `literature/stacks-project/decent-spaces.tex`:
Tag 08AL, including its proof; Tag 03I8; and Tag 03JV(6). The item deliberately
contains only the finiteness assertion of 08AL, not its final closed-immersion
assertion. The stage-1 split reviewed and merged from Q75 has no Lean record and
is preserved. The stage-2 handoff at the start of `coord/brief-stage2.md` explicitly
allows this assignment despite the previous worker's stage-1 refusal.

Hypotheses and conclusion, clause by clause:

- A scheme base is `{S : Scheme.{u}}`, and an algebraic space over it is
  `(X : AlgebraicSpace S)`, using the recorded category of fppf sheaves with
  representable diagonal and an étale surjective atlas.
- Decency is the explicit hypothesis `hdecent`. It quantifies over every
  `K : Type u`, `[Field K]`, base map `b : Spec (CommRingCat.of K) ⟶ S`, and
  field-valued map `c : yoneda.obj (Over.mk b) ⟶ X.obj.obj`. Every affine scheme
  over `S` is `U : Over S` with `IsAffine U.left`, and its arbitrary map to `X`
  is `t : yoneda.obj U ⟶ X.obj.obj`. The witnesses `V, p, q` with
  `IsPullback q (yoneda.map p) c t` represent precisely its sheaf fibre product
  with `Spec K`; `CompactSpace V.left` states quasi-compactness with no Hausdorff
  requirement. Representations are unique up to isomorphism, so requiring such
  a quasi-compact representation is exactly the affine test in the node.
- The specified field is `(L : Type u) [Field L]`. The specified morphism to `X`
  is `a : yoneda.obj (Over.mk b) ⟶ X.obj.obj`. Its composite to the base is the
  structure map `b` of `Over.mk b`; natural transformations on `Over S` are over
  `S`, so no extra unrelated map or compatibility assumption is introduced.
- Its base image point is `b (IsLocalRing.closedPoint L)`. The spectrum of a field
  has exactly that one point. `hs : IsClosed ({b (IsLocalRing.closedPoint L)} :
  Set S)` says the image is closed. The node does not fix a separately supplied
  point `s`; naming the unique image directly avoids an auxiliary equality.
- The induced extension is the canonical map
  `(S.descResidueField (Scheme.stalkClosedPointTo b)).hom` from the residue
  field at that image to `L`. `hfinite` asserts its `RingHom.Finite` property:
  `L` is a finite module over that residue field via this exact map. Over a
  field this is finite-dimensionality. No arbitrary algebra structure or
  arbitrary ring homomorphism is substituted.
- The conclusion is `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) a`.
  Expanding the recorded predicate gives, for every scheme `T : Over S` and
  map `h_T → X`, a representing scheme `U`, its projection `p : U ⟶ T`, and
  a presheaf pullback square, together with `IsFinite p.left`. These are
  exactly both clauses of the conclusion: representability and finiteness of
  every scheme-test projection. It does not require `T` to be affine or reduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`; this is publicly
  available through the recorded fibre-product module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` were read with their docstrings. This recorded
  statement dependency is publicly imported. Actual tests here use its shared
  `IsPullback` representability interface, so no separate fibre product or
  representation is defined.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, on the underlying scheme.
- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency is a Mathlib leaf).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (the same dependency also records `IsIntegralHom`, which is not needed in
  this statement). This module supplies the recorded scheme finiteness inputs
  `IsFinite.SpecMap_iff`, finite composition, and closed-immersion finiteness.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.descResidueField`; `Scheme.stalkClosedPointTo` from its stalk imports.
  The residue-field node is already a proof dependency; no dependency repair
  or duplicate canonical map is necessary.
- Plain proof imports include
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` for the field-point
  equivalence relation and
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective` for the recorded
  finite/radicial base-change node. The closed-immersion module is already
  included by the finite module. The three decent-space proof lemmas currently
  have no Lean record; no unavailable module is imported for them. Their
  five-step proof route is carried in the theorem's docstring for stage 3.

Edge cases checked against the mathematical statement: the empty algebraic
space admits no `a`, as required; the empty test scheme has empty pullback and
finite projection; equality `L = κ(s)` is included; purely inseparable finite
extensions are included; the base and test schemes can be nonreduced;
no separatedness, Noetherian, characteristic, or finite-type assumptions are
added. The universe is the shared `u` of the recorded algebraic-space site:
fields and test schemes range in that universe, not an independent smaller one.
No additional field extension universe is imposed.

Searches made before writing:

- `msearch.py`, LeanFinder: "Finite residue field extensions over a closed base
  point give finite morphisms to decent algebraic spaces". Eight hits, including
  scheme finiteness and residue-field results; none gives the algebraic-space
  theorem.
- `msearch.py`, Loogle: `"AlgebraicSpace", "IsFinite"`. Zero hits.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`:
  `IsDecent|finite_residue_field|finiteFieldMap`. Zero hits.
- `msearch.py`, LeanSearch: "A field valued point of a decent algebraic space
  over a closed base point with finite residue field extension is a representable
  finite morphism". Eight hits: scheme finiteness and
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, not the item.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `IsDecent|isDecent|[Dd]ecent|finiteFieldMap|finite_field_map`. Only the unrelated
  `SpaceFieldDiscretenessCriterion` and a private coefficient-field helper
  `PointFdMorphismDescent.finiteFieldMap` were found. Direct item-id search in
  `lean/WeilConjectures` found no declaration. The actual declaration names and
  full source signatures of the dependencies were inspected, rather than
  relying on their names.

No statement fault or `STATEMENT-DISPUTED` issue was found.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
