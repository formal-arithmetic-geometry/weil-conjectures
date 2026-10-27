## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGenerizationLifting` states
`AlgebraicGeometry.AlgebraicSpace.exists_generization_of_isOpenMap` with `sorry`.
No definition or theorem is proved. The node's statement, proof and proof dependencies
are unchanged. Its statement dependencies gain two already landed definition nodes:
`def-sfb-space-absolute-quasi-separated` and `def-sfb-proper-curve-moduli`, solely to use
`IsAbsolutelyQuasiSeparated` and the canonical `mapPoint` without duplicating them.

Clause-by-clause correspondence:

- The scheme and size convention are `{S : Scheme.{u}}`, with explicit `universe u`.
  The existing algebraic-space framework uses test schemes `Scheme.{u}`, presheaf
  values `Type u`, and point classes in `Type (u + 1)`. No universe equality is added.
- The spaces and their morphism are `(X Y : AlgebraicSpace S) (f : X ⟶ Y)`.
  This is the full subcategory of fppf sheaves with representable diagonal and an
  étale surjective atlas. Its arrows are natural transformations of sheaves.
- Both spaces are quasi-separated: `_hX : IsAbsolutelyQuasiSeparated X` and
  `_hY : IsAbsolutelyQuasiSeparated Y`. The imported definition tests compactness
  of `Point (Limits.pullback a b)` for every pair of affine schemes mapping to
  the space. Stacks Tag 0AHR(3) identifies this with quasi-compactness of the
  absolute diagonal over Spec Z. This also works when S is not quasi-separated;
  the hypotheses are not quasi-compactness of a relative diagonal over S.
- The explanatory quasi-compactness convention is the existing
  `CompactSpace (Point F)` for spaces and `MapIsQuasiCompact` for maps; the latter
  tests actual presheaf pullbacks along every affine scheme. It introduces no
  quasi-compactness hypothesis on X, Y or f in this theorem.
- The atlas topology is the imported `pointTopologicalSpace`. It is the final
  topology of all representable étale scheme tests, exactly the recorded topology.
- Openness of the point map is `_hf : IsOpenMap (mapPoint f.hom.hom)`.
  `mapPoint` applies the natural transformation to field representatives and
  descends it through the existing common-extension quotient.
- The specified points are `(x₀ : Point X.obj.obj) (y₁ : Point Y.obj.obj)`.
- The given specialization is
  `_h : mapPoint f.hom.hom x₀ ∈ closure ({y₁} : Set (Point Y.obj.obj))`.
- The conclusion quantifies `∃ x₁ : Point X.obj.obj`; its first conjunct is
  `x₀ ∈ closure ({x₁} : Set (Point X.obj.obj))`, and its second conjunct is
  `mapPoint f.hom.hom x₁ = y₁`.
- There is no surjectivity, representability, flatness, local finite presentation,
  quasi-compactness, separatedness, or quasi-separatedness of the base assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention,
  not a definition to import or instantiate; its universes are written above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; imported publicly as the recorded fibre-product
  statement dependency. Their signatures and docstrings were read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, `PointRepresentative.map`, `pointImage`.
  The point-class source was also read: `Point`, `PointRepresentative`, `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`,
  `AlgebraicSpace.MapIsQuasiCompact`.

The landed proof-dependency modules for affine étale atlases, point openness and
continuity, and constructible-topology comparison are imported privately. Scheme
quasi-separatedness and spectral constructible-topology Mathlib files supply the
recorded Mathlib proof leaves. The two proof nodes on space qcqs permanence and
quasi-compact constructible closedness have no recorded module yet; no module can
be imported for those. They are named in the complete four-step natural-language
proof in the theorem docstring, following the node without changing its argument.

Sources checked: local Stacks `morphisms.tex`, `lemma-open-generizing` (Tag 040F),
and online Stacks Tag 0AHR. Also read Rydh's actual paper at
https://davidrydh.se/papers/submersion20100305.pdf, section 1 before Remark (1.3),
Remark (1.8), Remark (2.5)(2), and the extension at the end of section 2.
The item is a supporting node, not the blueprint unit's own assertion.

Edge cases checked before writing: an empty source has no x₀, and an empty target
has no y₁; neither is excluded by a nonemptiness binder. If y₁ equals f(x₀), x₁=x₀
is permitted. Identity maps and open immersions fit the formulation. A proper open
image need not be the whole target; closure under generalization keeps the required
y₁ in that image, so no surjectivity was added. The compactness argument includes
the empty finite intersection by using all of the affine chart. Arbitrary base S,
including a non-quasi-separated base, is allowed. The closure direction is exactly
that of generalization lifting, not specialization lifting.

Searches actually run with msearch.py (Q32, this item):

- LeanFinder: `An open morphism of quasi separated algebraic spaces lifts
  generalizations through a specified point`: 8 hits, principally
  `AlgebraicGeometry.isOpenMap_of_generalizingMap` (opposite direction and locally
  finite presentation) and `Flat.generalizingMap` (extra flatness). No match.
- Loogle: `IsOpenMap, GeneralizingMap`: 1 hit,
  `AlgebraicGeometry.isOpenMap_of_generalizingMap`; no exact match.
- Mathlib grep: `generalizingMap|generizing`, subdirectory `AlgebraicGeometry`:
  12 hits, on the converse openness criterion, flat maps and local properties.
- LeanSearch: `An open morphism of algebraic spaces lifts generalizations of points`:
  8 hits, on the converse criterion, universally open scheme maps being open,
  and open-immersion lifts. No algebraic-space generalization-lifting theorem.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `exists_generization_of_isOpenMap|open.*generiz|generiz.*open`: no exact statement
  or collision. The relevant project hit is the consumer's proof docstring.
- Direct grep for this item ID in `lean/WeilConjectures`: no hits. Earlier direct
  rg for `generalizingMap` found flat-scheme applications only.
- Direct rg in project algebraic-space modules found the existing canonical
  `mapPoint` and `IsAbsolutelyQuasiSeparated`, which are reused.

No STATEMENT-DISPUTED finding and no statement correction. No new nodes or dependency
repairs are needed.

Validation: scompile.py compiled the delivered module both as a sandbox module and
with its final library module name, with no errors or unexpected warnings. All binders
and universes are explicit, and autoImplicit is disabled. The only proof is `sorry`.

## Second reading by Q32

The dispatcher explicitly requires this worker to deliver without spawning another
agent; independent review is performed by the maintainer. This section records a
second self-reading, not a claim of an independent worker review.

With the JSON and Lean file open, checked the two absolute quasi-separatedness
binders against the node's absolute diagonal convention and Tag 0AHR(3), and checked
that the point topology and point map are the landed objects. The hypothesis uses
f(x₀) in closure {y₁}; the existential uses x₀ in closure {x₁} followed by f(x₁)=y₁,
so both orientations and the specified source point are retained. The two newly
cited nodes already exist and contain exactly the helper definitions used. The
whole statement needs no extra hypothesis and drops no conclusion. No mismatch
was found and no further change was made on this reading.
