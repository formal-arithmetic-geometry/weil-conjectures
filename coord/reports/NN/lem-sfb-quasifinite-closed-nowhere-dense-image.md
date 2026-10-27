## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteClosedNowhereDenseImage` states
`AlgebraicGeometry.Scheme.Hom.isNowhereDense_image_of_isQuasiFinite`, with its proof
entirely `sorry`. No definitions, additional nodes, dependency repairs or statement
corrections are needed. The node copy changes only `lean`.

I read the statement and all six proof steps of the item, Stacks Project
`morphisms.tex`, Tag 03J2 (`lemma-image-nowhere-dense-quasi-finite`, lines 15254ff),
and both statement-dependency records and their actual declarations. The source
has precisely the node's assertion. The declaration docstring carries the six
accepted proof steps, with their named inputs and the local topology arguments.

The correspondence of every hypothesis and clause is:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with the universe `u` explicitly declared.
  A common arbitrary universe is the library's category-of-schemes convention.
- The morphism f from Y to X: `(f : Y ⟶ X)`.
- Quasi-finiteness: `(hf : f.IsQuasiFinite)`, exactly the predicate recorded by
  `pqf-def-quasifinite`, not Mathlib's less restrictive `LocallyQuasiFinite`.
  Reading the actual definition shows it is `LocallyOfFiniteType f ∧ QuasiCompact f ∧
  ∀ y, IsOpen {f.asFiber y}` in the scheme fibre. Thus it includes finite type and
  every point isolated in its fibre, as required by clause (3) of that dependency.
- The subset of the underlying space of Y: `(T : Set Y)`.
- Closedness: `(hT : IsClosed T)`.
- Nowhere denseness of T: `(hTd : IsNowhereDense T)`. Mathlib's definition in
  `Topology/GDelta/Basic.lean:200` is exactly `interior (closure T) = ∅`.
- The conclusion: `IsNowhereDense (f '' T)`, where the coercion of f is its
  underlying map of topological spaces, and `''` is set-theoretic image.
- The statement asserts no closedness of the image: the sole conclusion is
  nowhere denseness, with the closure included by its definition.
- Empty schemes and the empty subset: there are no `Nonempty`, inhabitedness,
  nonzero-ring, or nonempty-set binders. The empty subset has empty image and
  satisfies Mathlib's `isNowhereDense_empty`. An empty target forces an empty
  source for any morphism, which is allowed by the same signature.

Statement dependencies actually used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. Read the locally
  affine locally ringed space structure at Scheme.lean:36–47 and the morphism
  structure/category at lines 73–94.
- `pqf-def-quasifinite`:
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`, declaration
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`. Read the entire module, including
  the docstring and the full definition; no copy or replacement of it is made.
- The additional public import `Mathlib.Topology.GDelta.Basic` provides the
  existing notion `IsNowhereDense`; no new notion is introduced.

Proof-plan imports: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` supplies
`locallyOfFiniteType_iff` and the finite-type notion;
`Mathlib.AlgebraicGeometry.Morphisms.Affine` supplies
`isAffineHom_of_isAffine`, affine base-change stability, affine-source and
quasi-compactness results; `Mathlib.AlgebraicGeometry.Morphisms.Separated` supplies
the separation clause of affine-morphism permanence;
`Mathlib.AlgebraicGeometry.Fiber` supplies `Scheme.Hom.fiber` and its projections;
`Mathlib.AlgebraicGeometry.OpenImmersion` supplies `IsOpenImmersion`; and
`WeilConjectures.AlgebraicGeometry.QuasiFiniteAffineOpenInFinite` supplies
`Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine` (I read its
full signature and docstring). These are plain imports, as required for proof
inputs. `lem-sfb-finite-image-nowhere-dense` has no Lean record or Mathlib match in
the read repository and hence supplies no module import yet; it remains named
in the proof docstring and in the unchanged proof dependencies. It is needed
only for the future proof, not to type this statement.

Edge cases checked before writing: empty X, empty Y, empty T, and the empty
finite cover in the proof. The identity morphism reduces the conclusion to the
nowhere-denseness hypothesis. No affine, Noetherian, separated, flat, reduced,
integral or surjectivity hypothesis was imposed. The finite-image factorization
argument uses closure in the intermediate scheme, so it does not accidentally
strengthen the conclusion to closedness. The finite-type/quasi-compact part of
quasi-finiteness is retained: over an infinite field, an infinite disjoint union
of affine lines mapping identically to one affine line allows the closed union
of distinct rational points, one per component, to have dense image. This shows
why local quasi-finiteness alone cannot
replace the recorded hypothesis.

Searches actually run through `msearch.py`, with this group and item:

- LeanSearch: `A quasi finite morphism of schemes sends closed nowhere dense
  subsets to nowhere dense subsets`. Eight hits; these give
  `LocallyQuasiFinite`, its constructors, finite maps and closed-map criteria.
  None states this preservation theorem.
- LeanFinder: `The image of a closed nowhere dense subset under a quasi finite
  morphism of schemes is nowhere dense`. Eight hits; these concern dominance,
  quasi-finiteness, schematic images and constructibility, not this statement.
- Loogle: `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite, IsNowhereDense`. Zero hits,
  with the explicit diagnostic that Loogle does not know the project-specific
  `IsQuasiFinite` identifier. This is not evidence that the predicate is absent
  locally: its actual source and dependency record were read and used.
- Mathlib grep: `IsNowhereDense|nowhere_dense|nowhereDense` in `AlgebraicGeometry`.
  Zero hits. I also read `Topology/GDelta/Basic.lean:195–262`; its
  `Topology.IsInducing.isNowhereDense_image` requires an inducing map, which a
  quasi-finite morphism need not be, so it is not an existing match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `IsNowhereDense`, `nowhere.?dense`, the item id, and
  `isNowhereDense_image|isNowhereDense.*[Qq]uasi|[Qq]uasi.*[Nn]owhere` found only
  unrelated uses, inducing-map results, and a citation to this item in the
  strict-henselian section-density proof. No existing declaration states it.
- Searched `dag/lean_names_upstream.json`, both project roots and Mathlib for
  `isNowhereDense_image_of_isQuasiFinite|QuasiFiniteClosedNowhereDenseImage`:
  no name conflict. The item-id search in `WeilConjectures` found no declaration.

No node fault or statement dispute was found. All binders and the universe are
explicit, and `autoImplicit` is disabled in the module.

Validation: `scompile.py` compiled the file separately in sandbox and library
module mode, each in 1.3 seconds, with exit code zero and no unexpected warnings.
The node signature is copied verbatim from the declaration, all Lean lines have
length at most 100, and the only changed node field is `lean`.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
