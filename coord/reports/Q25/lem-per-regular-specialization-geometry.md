## Worker report

The delivery states `AlgebraicGeometry.RegularSpecializationGeometry.regular_specialization_geometry`
in `Sheaf.AlgebraicGeometry.RegularSpecializationGeometry`. Its only theorem proof is `sorry`.
Definitions contain real data. The node's mathematical statement and proof are unchanged.
The retained modules were checked against the current DAG and published source, then compiled
separately through scompile.py. Both files compiled cleanly (no unexpected warnings).

Hypotheses correspond as follows:

- `P X : Scheme.{u}` and `r : P ⟶ X` introduce the two schemes and their morphism.
- `[IsNoetherian P] [IsNoetherian X]` impose exactly Noetherianity, including quasi-compactness.
- `hP : ∀ U : P.affineOpens, IsExcellent Γ(P,U)` and the analogous `hX` give excellence.
  Excellence of a scheme can equivalently be checked on every affine open; these use the
  recorded excellent-ring predicate, without a finite-type assumption on `r`.
- `[Flat r]` is the recorded flat-morphism class.
- `hregular` ranges over every `x : X`, field `L : Type u`, its residue-field algebra structure,
  and `[Module.Finite (X.residueField x) L]`. It asserts `IsRegularScheme` for the pullback of
  `r.fiberToSpecResidueField x` along `Spec.map (algebraMap _ L)`. This is exactly regularity
  of fibres after all finite residue-field extensions. It includes the identity extension.

The notions and each conclusion correspond as follows:

- The new `StrictGeometricPointData` bundles the recorded inline geometric point (an
  algebraically closed field and a Spec morphism). `StrictGeometricPoint` uses Mathlib's
  `InducedCategory (Over S)` on the existing strict localizations. Its arrows are precisely
  maps of strict localizations over `S`, and category isomorphisms mean precisely such
  isomorphisms. There is no algebraicity or transcendence restriction on the fields.
- `underlying` is the image of the unique field-spectrum point. `closed` is its canonical
  evaluation lift to the existing strict localization. `specializationSlice` converts each
  category arrow to the published `OrientedNearbyCycles.SliceSpecialization`; it does not
  construct an alternative strict localization or an alternative specialization datum.
- `codimension a` is `topologicalKrullDim` of the closure of the image of the distinguished
  source point under the strict-local map `a`. This is the dimension of the reduced closure:
  nilpotents do not change its topological space. `IsImmediate a` means dimension one.
- `PointMap r p x` specifies a local map of strict localizations over `r`: `over` is the
  structural-map equation and `closed` requires closed point to closed point. This is the
  strict-local description of the specified map of geometric points, with no replacement
  by an unconstrained map. `LiesOver a s vp vq` is the commutative square of the four actual
  strict-local maps, retaining the specified base specialization.
- `fibreLocalDimension r p` is `ringKrullDim` of the stalk of the actual scheme-theoretic
  fibre at `r.asFiber p.underlying`. Thus it is the stated `b(p)`, not dimension of a global
  fibre or a chosen strict-local model. `IsFibreGeneric r p` asserts that this is zero.
- The first conjunct `HasGenericSquares r` quantifies over every `a : p ⟶ q`, `s : x ⟶ y`
  and the compatible endpoint maps. Its witnesses `ep,eq` are the two fibre-generic points;
  `h,l,k` are the top, left and right arrows. `h ≫ k = l ≫ a` is the required equality of
  composites. `LiesOver h s bp bq` puts the upper arrow over the given base arrow.
  `l.hom.left ≫ vp.map = bp.map` and `k.hom.left ≫ vq.map = bq.map` place the vertical
  arrows in the respective fibres. Its last two equations give their codimensions
  `b(p)` and `b(q)`, in the order specified by the node.
- `HasUniqueGenericLifts r` starts with every fibre-generic target and every base arrow.
  It gives a fibre-generic source, a lift over that arrow, equality of its codimension
  with the base codimension, and, for any competing generic lift, an isomorphism
  commuting both with the target arrow and the base-point map. Existence of this
  isomorphism is asserted; uniqueness of the isomorphism is not asserted.
- `HasImmediateGenericFactorizations r` quantifies over every specified generic arrow and
  every finite downstairs factorization `D : ComposableArrows ... n`. The endpoint
  isomorphisms and total-arrow equation preserve the specified whole arrow. Its witness
  `E` has the same length, fibre-generic vertices, immediate edges, commuting squares
  over every map of the indexing category, and the two endpoint compatibility equations.
- `HasCodimensionFormula r` first identifies the actual extended Krull dimensions with
  natural numbers `cp,cx,bp,bq`. It then states `(cp : ℤ) = cx + bq - bp`. This keeps
  subtraction in the integers, as required, without silently assigning zero to infinity.
  Finiteness follows from local Noetherianity of the strict-local closures and local rings.

Dependency declarations actually used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, with its existing quasi-excellence and
  universally-catenary predicates (def-exc-excellent-ring).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`; the source's
  `Flat.iff_flat_stalkMap` identifies its affine definition with the node's stalk definition.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, namely
  `IsLocallyNoetherian X ∧ IsRegular X` (def-weil-regular-scheme).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`, `asFiber`,
  and `fiberHomeo` (def-pc-scheme-fibre). Stalks are Mathlib's presheaf stalks.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded geometric-point
  convention is the inline field/Spec map. `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` confirms its residue-field interpretation.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme` and
  `strictHenselizationRing` reuse the recorded pointed-neighbourhood construction.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, the published structural map.
- `Sheaf.Paper.StrictHenselizationPointEvaluation`: `Scheme.strictHenselizationPointEvaluation`,
  the map defined by the colimit universal property; its Spec map supplies `closed`.
- `Sheaf.Paper.GeneralNearbySliceTest`: `OrientedNearbyCycles.SliceSpecialization`, whose
  existing fields are used verbatim by `specializationSlice`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; `Mathlib.Topology.KrullDimension`:
  `topologicalKrullDim`, the supremum of chains of irreducible closed subsets.
- `Mathlib.CategoryTheory.InducedCategory` and `ComposableArrows.Basic`: the category
  construction and finite chains; no second category-theory definitions are introduced.

The four proof-dependency nodes have no recorded Lean modules at this time. They are
referenced by identifier in the complete natural-language proof docstring; no import can
be added for an absent module. They are proof inputs, not additional theorem hypotheses.

Edge cases checked: an empty source has no geometric points and all four conclusions are
vacuous. With no compatible target points the corresponding quantifiers are also vacuous.
Identity arrows and geometric isomorphisms are included in the induced category and have
codimension zero. `n = 0` is allowed in `ComposableArrows` and its endpoint/total-arrow
condition retains the identity or isomorphism case. For a smooth curve over a field,
generic-to-closed gives `1 = 0 + 1 - 0`. For affine space over a trait, the signs agree
with `2 = 1 + 1 - 0` and `1 = 1 + 1 - 1`. Arbitrary characteristic and finite inseparable
residue extensions are included. All schemes and geometric fields use the same universe,
so a smaller independent test-field universe cannot make regularity vacuous. The source
may have arbitrary geometric overfields; varying `u` gives the usual universe convention.

Searches: the retained msearch log includes LeanFinder on regular-morphism generic lifting,
Loogle `"Specialization", "Scheme"` (zero hits), and Mathlib grep for
`GeometricSpecialization|geometricSpecialization|IsRegularMorphism` (zero hits).
Fresh LeanSearch and LeanFinder searches for the category of geometric points with maps of
strict localizations returned ordinary stalk-specialization and specializing-map lemmas,
not this category or this theorem. Fresh Mathlib/AlgebraicGeometry grep for
`StrictGeometricPoint|GeometricSpecialization|SpecializationCategory` returned zero hits.
Upstream WeilConjectures grep for these names and the item id returned no matches.
Project lean/Sheaf searches found `SliceSpecialization`, which is reused, and individual
immediate-specialization statements, but no category or regular lifting theorem. DAG searches
found the inline specialization convention in def-per-potential-dualizing, which has no Lean
record and does not define the category with its composition and isomorphisms.
`tools/blueprint_refs.py search 'geometric specialization'` returned zero blueprint nodes.
The fresh category searches and their tool outputs are recorded in the new node.

No statement correction, disputed statement, dependency interface replacement, or extra
hypothesis is introduced. All helpers in the main module belong to the one theorem's
four-clause statement and are listed in `lean.declarations`.

## New nodes

`def-per-geometric-specialization-category` packages the category needed to express
composition, isomorphism and finite factorizations, and its codimension/immediacy predicate.
Its source is ILO XIV, Definitions 2.1.1–2.1.2, printed pp.209–210. These definitions were
read with XVII the project server–the project server, printed pp.284–285, and XIV Proposition 2.5.4, printed
pp.217–218. The new category uses the existing inline geometric-point convention, strict
localizations, structural maps, evaluation and individual `SliceSpecialization` data.
The searches above found no existing category, so Mathlib's `InducedCategory` constructs
it with real data. The new node is cited directly by the item. Its source mentions the
underlying topological dimension because reduction does not affect dimension; this
introduces no alternative ring-dimension predicate. No independent theorem is postponed
in the new definition module.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
