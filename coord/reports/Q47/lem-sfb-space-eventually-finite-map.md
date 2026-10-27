## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEventuallyFiniteMap` states
`AlgebraicGeometry.AlgebraicSpace.exists_eventually_isFinite_baseChange`, with `sorry`.
It adds no definitions, hypotheses, independent helpers, or nodes. The natural-language
proof in the declaration docstring follows all five accepted DAG proof steps.

The inherited BLOCKED ending concerned reopening the accepted stage-1 split.
`coord/brief-stage2.md` §0 now explicitly distinguishes that from this stage-2 task.
The current node has `status: split`, a passing stage-1 review dated 2026-10-23,
no `lean` record, and a stage-2 row in `coord/queue.tsv`. No repair note is present.
The accepted statement, split, dependencies, and all other node fields are preserved.
The example CompactObject module was read; it is currently withdrawn, so the working
module-mode header follows the current §4 instructions and landed algebraic-space modules.

Source read: `literature/stacks-project/spaces-limits.tex`, Situation
`situation-descent-property` (084W), lines 1448–1457, and
`lemma-descend-finite` (084Z), lines 1647–1667. The node includes all-stage qcqs
assumptions and persistence after the first finite stage, exactly as its accepted split.
For the absolute quasi-separatedness encoding I also read
`literature/stacks-project/spaces-properties.tex`, `lemma-characterize-quasi-separated`,
lines 132–165: its condition (3) is the arbitrary affine-pair test used below.
This is also the public signature used by the landed
`Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit` module.

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`. Every space is `AlgebraicSpace S`, the
  recorded full subcategory of big-fppf sheaves with representable diagonal and
  surjective etale scheme atlas. Morphisms have the recorded natural transformations.
- The size convention is the explicit universe `u` on schemes and `I : Type u`,
  with the existing presheaf `Type u` and point-class `Type (u + 1)` encodings.
  No equality of separately specified universes or size condition is imposed.
- A small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. No antisymmetry is needed.
- The inverse system is `D : Iᵒᵖ ⥤ AlgebraicSpace S`. `D.obj (op i)` is B_i.
  Its functor laws supply identities and transition compatibility.
- All B_i are quasi-compact by `hBqc : ∀ i, CompactSpace (Point ... )`.
  With the recorded final point topology, `CompactSpace` is precisely the finite
  subcover condition for arbitrary open covers, including the empty space.
- All B_i are absolutely quasi-separated by `hBqs`: for every pair of affine
  schemes U, V mapping to B_i, `Point (Limits.pullback a b)` is compact.
  The Stacks affine-pair characterization above identifies this with quasi-compactness
  of the diagonal over Spec Z. This is not a diagonal over S: the maps U and V
  are arbitrary maps to B_i, each carrying the induced S-structure. The same exact
  criterion appears in `hXqs` and `hYqs` for X_0 and Y_0. In particular S need not
  be quasi-separated.
- Affine transitions are `haff`: for every transition `D.map g`,
  `IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map g).hom.hom`.
  This requires an actual scheme representation of every scheme test and an affine
  scheme projection. It is equivalent to the stated affine-test condition, since
  scheme affineness is local on the target, and includes representability.
- The limit B and its projections are the cone `c : Cone D`; `hc : IsLimit c`
  states its full categorical universal property for algebraic spaces over S.
  The chosen index is `i₀ : I`.
- X_0, Y_0, and f_0 are `X₀ Y₀ : AlgebraicSpace S`, `f₀ : X₀ ⟶ Y₀`.
  `y₀ : Y₀ ⟶ D.obj (op i₀)` is their structure map to B_i0; X_0 has the
  structure map `f₀ ≫ y₀`. Thus this is exactly a morphism over B_i0:
  specifying an additional structure map on X_0 and its commuting equation would
  specify the same data. No condition on the choice of structure maps is added.
- X_0 and Y_0 are quasi-compact by `hXqc` and `hYqc`, and absolutely
  quasi-separated by the affine-pair conditions `hXqs` and `hYqs`.
- Local finite type is `hlft : MapIsLocally (@LocallyOfFiniteType) f₀`.
  This uses every compatible pair of representable etale scheme charts exactly
  as the recorded dependency defines it; it does not assume finite presentation.
- The initial map in the over-category of sheaves is
  `Over.homMk (U := Over.mk (f₀.hom ≫ y₀.hom))
  (V := Over.mk y₀.hom) f₀.hom rfl`.
  Its commuting equation is reflexivity because the source structure map is the
  composite. `Over.pullback` constructs the actual canonical sheaf fibre products
  and the induced arrow; its result's `.left.hom` is the underlying presheaf map.
  Fibre products remain algebraic spaces by the recorded fibre-product theorem.
- In `hfinite`, pulling back this over-category map along
  `(c.π.app (op i₀)).hom` is exactly f over B. Its finiteness is
  `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) ...`:
  every scheme test has an actual representing scheme with finite projection,
  using the recorded Mathlib scheme predicate. No arbitrary replacement arrow
  or additional assumption is supplied.
- The conclusion is `∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hji : j ≤ i), ...`.
  The pullback is along `(D.map (homOfLE (le_trans hj hji)).op).hom`, the actual
  transition from B_i to B_i0. The same scheme-test finiteness predicate states
  that every such f_i is finite, including i = j.
- The explanatory definitions of quasi-separated morphism and finite presentation
  in the node impose no extra hypotheses on f_0. There is no finite-presentation
  assumption in the signature. The only local property needed is local finite type.

Recorded dependency declarations used (signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and `AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`; also read
  `etaleCover_pullback` and `etale_fibreProduct_isScheme` and their full docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, using the existing `Point` classes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`; its imports also supply
  `ProperCurveModuli`'s `AlgebraicSpace.MapIsQuasiCompact` (read in full).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  Also read the recorded `IsIntegralHom` signature in Morphisms/Integral.lean.
- `def-weil-size-convention` has no declaration, as its `lean.convention` record
  explains; the universes above implement that convention.
- Canonical maps use Mathlib's `CategoryTheory.Over.pullback` and `Over.homMk`,
  whose full definitions were read; the system uses `Cone`, `IsLimit`, `op`,
  and `homOfLE` from Mathlib.

Statement dependencies are public imports, directly or through the morphism-property
module's public imports. Plain proof imports include the recorded upstream
`WeilConjectures.AlgebraicGeometry.DescendFinite` (read its full signature and proof
outline) and the Mathlib modules of the affine-scheme qcqs proof leaf. Other proof
nodes have neither a `lean` record nor a Mathlib match in the current DAG, so there
is no recorded module to import for them. They are cited by id in the proof docstring;
no missing proof node is used as an additional hypothesis.

Edge cases checked before writing:

- Empty X_0 or Y_0: compactness and absolute quasi-separatedness allow empty
  point sets; no nonempty space or atlas is assumed. With empty Y_0 a map f_0
  has empty source, and the claim is still the expected finite-map statement.
- Singleton index and constant systems: j may equal i_0. The conclusion includes
  equality indices, and identity transitions give the same morphism up to the
  canonical base-change isomorphism.
- General preorder: equivalent indices need not be equal; functoriality handles
  their inverse transition isomorphisms. No chosen upper bound operation is required.
- The empty index is excluded exactly by the node's nonemptiness and chosen i_0.
- An arbitrary, possibly non-quasi-separated base S is allowed; no relative-S
  diagonal is substituted for the absolute quasi-separatedness hypothesis.
- No compactness of the limit, finite type of the spaces over S, finite presentation
  of f_0, or representability of f_0 at the initial stage is assumed.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: "A locally finite type morphism of qcqs
  algebraic spaces whose base change to an inverse limit with affine transitions
  is finite becomes finite at a sufficiently late stage". Eight hits, including
  `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`,
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`, `locallyOfFiniteType_iff`,
  `IsFinite`, and `LocallyOfFiniteType`. These are scheme statements, not this
  algebraic-space inverse-limit assertion.
- `msearch.py ... loogle` query `"IsFinite", "LocallyOfFiniteType"`: three hits,
  `IsFinite.instLocallyOfFiniteType`,
  `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`, and
  `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`; none concerns this limit.
- `msearch.py ... grep` query
  `AlgebraicSpace|eventually.*[Ff]inite|descend.*[Ff]inite`, subdirectory
  `AlgebraicGeometry`: six hits in AffineTransitionLimit.lean, LocalFlatDescent.lean,
  and FlatDescent.lean; these concern schemes and descent of scheme properties.
- `msearch.py ... leansearch` query: "finite morphisms of algebraic spaces descend
  along directed inverse limits with affine transition maps". Eight hits, including
  `HasAffineProperty.descendsAlong_of_affineAnd`, `Scheme.compactSpace_of_isLimit`,
  `exists_appTop_π_eq_of_isLimit`, and `IsFinite`; none is the requested statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `eventually.*[Ff]inite|[Ff]inite.*eventually|descend.*[Ff]inite` found the
  upstream scheme descent theorem and unrelated finiteness results, not this
  statement. The exact blueprint-id search in both trees found no declaration.
  Further source searches for `IsRepresentableWith`, `IsFinite`, affine maps,
  point compactness and quasi-separatedness found the existing interfaces cited above,
  including the affine-pair encoding in IntegralSpaceFinitePresentationLimit;
  no notion was duplicated.

Validation: `scompile.py Q47 lem-sfb-space-eventually-finite-map <module>` compiled
both its sandbox and library-path versions cleanly (7.8 s and 8.2 s), with no errors
or unexpected warnings. The file explicitly sets `autoImplicit false`, uses no
`let` or `show` in the statement, and has no line over 100 characters.
No statement correction, disputed assertion, new node, or dependency repair is needed.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
